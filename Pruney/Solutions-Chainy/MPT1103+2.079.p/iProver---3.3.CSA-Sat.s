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
% DateTime   : Thu Dec  3 12:11:00 EST 2020

% Result     : CounterSatisfiable 3.48s
% Output     : Saturation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  247 (5729 expanded)
%              Number of clauses        :  153 (1224 expanded)
%              Number of leaves         :   31 (1602 expanded)
%              Depth                    :   18
%              Number of atoms          :  478 (8598 expanded)
%              Number of equality atoms :  377 (6417 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f80])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f82])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f83])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f85])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f86])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f61,f89])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f60,f89])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f59])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k1_xboole_0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f69,f89])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f88])).

fof(f12,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f84])).

fof(f91,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f57,f87])).

fof(f13,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f59])).

fof(f100,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f28,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k2_struct_0(X0) = sK1
            & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) )
          | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)
            & k2_struct_0(X0) != sK1 ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k2_struct_0(sK0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)
              & k2_struct_0(sK0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f44,f43])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f85])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_203,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_461,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_815,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_819,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1973,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k7_subset_1(X1,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_815,c_819])).

cnf(c_2194,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(X2,k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1973,c_1973])).

cnf(c_5,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_822,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_836,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_822,c_4])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_818,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2297,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,k1_xboole_0),X1) = k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_815,c_818])).

cnf(c_2311,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X1)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2297,c_4])).

cnf(c_2326,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_836,c_2311])).

cnf(c_3567,plain,
    ( k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_2194,c_2326])).

cnf(c_5237,plain,
    ( k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3567,c_3567])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_817,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_subset_1(X1,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5290,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5237,c_817])).

cnf(c_7020,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1973,c_5290])).

cnf(c_1975,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_836,c_819])).

cnf(c_7048,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7020,c_1975])).

cnf(c_13,plain,
    ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k1_xboole_0) = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_816,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X1
    | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_868,plain,
    ( X0 = X1
    | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_816,c_4])).

cnf(c_5289,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(X0,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5237,c_868])).

cnf(c_6879,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1973,c_5289])).

cnf(c_6892,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6879,c_1975])).

cnf(c_5235,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_817])).

cnf(c_5702,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X2,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_5235])).

cnf(c_6665,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X2,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X3,k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_5702])).

cnf(c_5234,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k4_subset_1(X1,X1,X1),k7_subset_1(X0,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_868])).

cnf(c_5680,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k4_subset_1(X1,X1,X1),k7_subset_1(X2,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_5234])).

cnf(c_6633,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(X3,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_5680])).

cnf(c_2841,plain,
    ( k3_subset_1(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_1973,c_2326])).

cnf(c_4875,plain,
    ( k3_subset_1(X0,k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_2841,c_1975])).

cnf(c_4883,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4875,c_817])).

cnf(c_5523,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_4883])).

cnf(c_6301,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0))) != iProver_top
    | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_5523])).

cnf(c_4882,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0
    | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4875,c_868])).

cnf(c_5502,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0
    | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X1,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_4882])).

cnf(c_6265,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0
    | r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X2,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_5502])).

cnf(c_2844,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2326,c_817])).

cnf(c_5365,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_2844])).

cnf(c_5974,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_5365])).

cnf(c_2843,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = X0
    | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2326,c_868])).

cnf(c_5147,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = X0
    | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X1,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_2843])).

cnf(c_5869,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = X0
    | r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X2,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3567,c_5147])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_820,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2405,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X1,k1_xboole_0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_815,c_820])).

cnf(c_3810,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_815,c_2405])).

cnf(c_2,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3939,plain,
    ( k4_subset_1(X0,k1_xboole_0,k1_xboole_0) = k3_tarski(k1_zfmisc_1(k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_3810,c_2])).

cnf(c_3,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3940,plain,
    ( k4_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3939,c_3])).

cnf(c_2299,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X0),X1) = k3_subset_1(X0,k7_subset_1(X0,X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_818])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_821,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1683,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_815,c_821])).

cnf(c_1691,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1683,c_4])).

cnf(c_2302,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,X1)) = k4_subset_1(X0,k1_xboole_0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2299,c_1691])).

cnf(c_3680,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_815,c_2302])).

cnf(c_4431,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3940,c_3680])).

cnf(c_4480,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0
    | r1_tarski(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4431,c_868])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_101,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_14])).

cnf(c_812,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_831,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_812,c_4])).

cnf(c_5003,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0
    | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4480,c_831])).

cnf(c_2407,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_820])).

cnf(c_4421,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_836,c_2407])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_814,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2406,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_820])).

cnf(c_2933,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_814,c_2406])).

cnf(c_4900,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_4421,c_2933])).

cnf(c_3812,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_836,c_2405])).

cnf(c_3682,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,X0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_836,c_2302])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3147,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1975])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3156,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3147,c_1])).

cnf(c_3684,plain,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3682,c_4,c_3156])).

cnf(c_3814,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3812,c_3684])).

cnf(c_3811,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_814,c_2405])).

cnf(c_4502,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_3814,c_3811])).

cnf(c_3681,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_814,c_2302])).

cnf(c_4635,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4502,c_3681])).

cnf(c_3792,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_817])).

cnf(c_4634,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4502,c_3792])).

cnf(c_3791,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_868])).

cnf(c_4633,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
    | r1_tarski(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4502,c_3791])).

cnf(c_4419,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_815,c_2407])).

cnf(c_2324,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_815,c_2311])).

cnf(c_2193,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_zfmisc_1(k1_xboole_0))) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_1973])).

cnf(c_1328,plain,
    ( k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_2198,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2193,c_1328])).

cnf(c_2199,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2198,c_1])).

cnf(c_2332,plain,
    ( k4_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2324,c_4,c_2199])).

cnf(c_4427,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4419,c_2332])).

cnf(c_2932,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_815,c_2406])).

cnf(c_4573,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_4427,c_2932])).

cnf(c_4481,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,X0,k1_xboole_0),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4431,c_817])).

cnf(c_4420,plain,
    ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_814,c_2407])).

cnf(c_2325,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_814,c_2311])).

cnf(c_3570,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_2194,c_2325])).

cnf(c_3655,plain,
    ( k7_subset_1(X0,k1_xboole_0,sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X0,k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_868])).

cnf(c_4083,plain,
    ( k7_subset_1(X0,k1_xboole_0,sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X1,k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_3655])).

cnf(c_3656,plain,
    ( k7_subset_1(X0,k1_xboole_0,sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_817])).

cnf(c_4014,plain,
    ( k7_subset_1(X0,k1_xboole_0,sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_3656])).

cnf(c_3815,plain,
    ( k4_subset_1(X0,k1_xboole_0,X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3814,c_2405])).

cnf(c_2866,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2325,c_817])).

cnf(c_3569,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_2866])).

cnf(c_2865,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2325,c_868])).

cnf(c_3568,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X0,k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_2865])).

cnf(c_1974,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_814,c_819])).

cnf(c_3144,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1975,c_1974])).

cnf(c_2298,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_818])).

cnf(c_3055,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_836,c_2298])).

cnf(c_3237,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) ),
    inference(demodulation,[status(thm)],[c_3144,c_3055])).

cnf(c_3053,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_815,c_2298])).

cnf(c_3236,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_3144,c_3053])).

cnf(c_3235,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3144,c_2298])).

cnf(c_3054,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_814,c_2298])).

cnf(c_2047,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_1974])).

cnf(c_2048,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2047,c_1])).

cnf(c_3059,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3054,c_2048])).

cnf(c_3060,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3059,c_4])).

cnf(c_2934,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_836,c_2406])).

cnf(c_1684,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_814,c_821])).

cnf(c_1991,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_817])).

cnf(c_1990,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_868])).

cnf(c_1977,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1975,c_819])).

cnf(c_1942,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_868])).

cnf(c_27,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1952,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1942,c_27])).

cnf(c_1953,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1952])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_811,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1564,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_836,c_811])).

cnf(c_16,negated_conjecture,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_951,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_814,c_811])).

cnf(c_970,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_16,c_951])).

cnf(c_1048,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_815,c_811])).

cnf(c_1418,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_970,c_1048])).

cnf(c_19,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f76])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/0.99  
% 3.48/0.99  ------  iProver source info
% 3.48/0.99  
% 3.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/0.99  git: non_committed_changes: false
% 3.48/0.99  git: last_make_outside_of_git: false
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options
% 3.48/0.99  
% 3.48/0.99  --out_options                           all
% 3.48/0.99  --tptp_safe_out                         true
% 3.48/0.99  --problem_path                          ""
% 3.48/0.99  --include_path                          ""
% 3.48/0.99  --clausifier                            res/vclausify_rel
% 3.48/0.99  --clausifier_options                    --mode clausify
% 3.48/0.99  --stdin                                 false
% 3.48/0.99  --stats_out                             all
% 3.48/0.99  
% 3.48/0.99  ------ General Options
% 3.48/0.99  
% 3.48/0.99  --fof                                   false
% 3.48/0.99  --time_out_real                         305.
% 3.48/0.99  --time_out_virtual                      -1.
% 3.48/0.99  --symbol_type_check                     false
% 3.48/0.99  --clausify_out                          false
% 3.48/0.99  --sig_cnt_out                           false
% 3.48/0.99  --trig_cnt_out                          false
% 3.48/0.99  --trig_cnt_out_tolerance                1.
% 3.48/0.99  --trig_cnt_out_sk_spl                   false
% 3.48/0.99  --abstr_cl_out                          false
% 3.48/0.99  
% 3.48/0.99  ------ Global Options
% 3.48/0.99  
% 3.48/0.99  --schedule                              default
% 3.48/0.99  --add_important_lit                     false
% 3.48/0.99  --prop_solver_per_cl                    1000
% 3.48/0.99  --min_unsat_core                        false
% 3.48/0.99  --soft_assumptions                      false
% 3.48/0.99  --soft_lemma_size                       3
% 3.48/0.99  --prop_impl_unit_size                   0
% 3.48/0.99  --prop_impl_unit                        []
% 3.48/0.99  --share_sel_clauses                     true
% 3.48/0.99  --reset_solvers                         false
% 3.48/0.99  --bc_imp_inh                            [conj_cone]
% 3.48/0.99  --conj_cone_tolerance                   3.
% 3.48/0.99  --extra_neg_conj                        none
% 3.48/0.99  --large_theory_mode                     true
% 3.48/0.99  --prolific_symb_bound                   200
% 3.48/0.99  --lt_threshold                          2000
% 3.48/0.99  --clause_weak_htbl                      true
% 3.48/0.99  --gc_record_bc_elim                     false
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing Options
% 3.48/0.99  
% 3.48/0.99  --preprocessing_flag                    true
% 3.48/0.99  --time_out_prep_mult                    0.1
% 3.48/0.99  --splitting_mode                        input
% 3.48/0.99  --splitting_grd                         true
% 3.48/0.99  --splitting_cvd                         false
% 3.48/0.99  --splitting_cvd_svl                     false
% 3.48/0.99  --splitting_nvd                         32
% 3.48/0.99  --sub_typing                            true
% 3.48/0.99  --prep_gs_sim                           true
% 3.48/0.99  --prep_unflatten                        true
% 3.48/0.99  --prep_res_sim                          true
% 3.48/0.99  --prep_upred                            true
% 3.48/0.99  --prep_sem_filter                       exhaustive
% 3.48/0.99  --prep_sem_filter_out                   false
% 3.48/0.99  --pred_elim                             true
% 3.48/0.99  --res_sim_input                         true
% 3.48/0.99  --eq_ax_congr_red                       true
% 3.48/0.99  --pure_diseq_elim                       true
% 3.48/0.99  --brand_transform                       false
% 3.48/0.99  --non_eq_to_eq                          false
% 3.48/0.99  --prep_def_merge                        true
% 3.48/0.99  --prep_def_merge_prop_impl              false
% 3.48/0.99  --prep_def_merge_mbd                    true
% 3.48/0.99  --prep_def_merge_tr_red                 false
% 3.48/0.99  --prep_def_merge_tr_cl                  false
% 3.48/0.99  --smt_preprocessing                     true
% 3.48/0.99  --smt_ac_axioms                         fast
% 3.48/0.99  --preprocessed_out                      false
% 3.48/0.99  --preprocessed_stats                    false
% 3.48/0.99  
% 3.48/0.99  ------ Abstraction refinement Options
% 3.48/0.99  
% 3.48/0.99  --abstr_ref                             []
% 3.48/0.99  --abstr_ref_prep                        false
% 3.48/0.99  --abstr_ref_until_sat                   false
% 3.48/0.99  --abstr_ref_sig_restrict                funpre
% 3.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/0.99  --abstr_ref_under                       []
% 3.48/0.99  
% 3.48/0.99  ------ SAT Options
% 3.48/0.99  
% 3.48/0.99  --sat_mode                              false
% 3.48/0.99  --sat_fm_restart_options                ""
% 3.48/0.99  --sat_gr_def                            false
% 3.48/0.99  --sat_epr_types                         true
% 3.48/0.99  --sat_non_cyclic_types                  false
% 3.48/0.99  --sat_finite_models                     false
% 3.48/0.99  --sat_fm_lemmas                         false
% 3.48/0.99  --sat_fm_prep                           false
% 3.48/0.99  --sat_fm_uc_incr                        true
% 3.48/0.99  --sat_out_model                         small
% 3.48/0.99  --sat_out_clauses                       false
% 3.48/0.99  
% 3.48/0.99  ------ QBF Options
% 3.48/0.99  
% 3.48/0.99  --qbf_mode                              false
% 3.48/0.99  --qbf_elim_univ                         false
% 3.48/0.99  --qbf_dom_inst                          none
% 3.48/0.99  --qbf_dom_pre_inst                      false
% 3.48/0.99  --qbf_sk_in                             false
% 3.48/0.99  --qbf_pred_elim                         true
% 3.48/0.99  --qbf_split                             512
% 3.48/0.99  
% 3.48/0.99  ------ BMC1 Options
% 3.48/0.99  
% 3.48/0.99  --bmc1_incremental                      false
% 3.48/0.99  --bmc1_axioms                           reachable_all
% 3.48/0.99  --bmc1_min_bound                        0
% 3.48/0.99  --bmc1_max_bound                        -1
% 3.48/0.99  --bmc1_max_bound_default                -1
% 3.48/0.99  --bmc1_symbol_reachability              true
% 3.48/0.99  --bmc1_property_lemmas                  false
% 3.48/0.99  --bmc1_k_induction                      false
% 3.48/0.99  --bmc1_non_equiv_states                 false
% 3.48/0.99  --bmc1_deadlock                         false
% 3.48/0.99  --bmc1_ucm                              false
% 3.48/0.99  --bmc1_add_unsat_core                   none
% 3.48/0.99  --bmc1_unsat_core_children              false
% 3.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/0.99  --bmc1_out_stat                         full
% 3.48/0.99  --bmc1_ground_init                      false
% 3.48/0.99  --bmc1_pre_inst_next_state              false
% 3.48/0.99  --bmc1_pre_inst_state                   false
% 3.48/0.99  --bmc1_pre_inst_reach_state             false
% 3.48/0.99  --bmc1_out_unsat_core                   false
% 3.48/0.99  --bmc1_aig_witness_out                  false
% 3.48/0.99  --bmc1_verbose                          false
% 3.48/0.99  --bmc1_dump_clauses_tptp                false
% 3.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.48/0.99  --bmc1_dump_file                        -
% 3.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.48/0.99  --bmc1_ucm_extend_mode                  1
% 3.48/0.99  --bmc1_ucm_init_mode                    2
% 3.48/0.99  --bmc1_ucm_cone_mode                    none
% 3.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.48/0.99  --bmc1_ucm_relax_model                  4
% 3.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/0.99  --bmc1_ucm_layered_model                none
% 3.48/0.99  --bmc1_ucm_max_lemma_size               10
% 3.48/0.99  
% 3.48/0.99  ------ AIG Options
% 3.48/0.99  
% 3.48/0.99  --aig_mode                              false
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation Options
% 3.48/0.99  
% 3.48/0.99  --instantiation_flag                    true
% 3.48/0.99  --inst_sos_flag                         false
% 3.48/0.99  --inst_sos_phase                        true
% 3.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel_side                     num_symb
% 3.48/0.99  --inst_solver_per_active                1400
% 3.48/0.99  --inst_solver_calls_frac                1.
% 3.48/0.99  --inst_passive_queue_type               priority_queues
% 3.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/0.99  --inst_passive_queues_freq              [25;2]
% 3.48/0.99  --inst_dismatching                      true
% 3.48/0.99  --inst_eager_unprocessed_to_passive     true
% 3.48/0.99  --inst_prop_sim_given                   true
% 3.48/0.99  --inst_prop_sim_new                     false
% 3.48/0.99  --inst_subs_new                         false
% 3.48/0.99  --inst_eq_res_simp                      false
% 3.48/0.99  --inst_subs_given                       false
% 3.48/0.99  --inst_orphan_elimination               true
% 3.48/0.99  --inst_learning_loop_flag               true
% 3.48/0.99  --inst_learning_start                   3000
% 3.48/0.99  --inst_learning_factor                  2
% 3.48/0.99  --inst_start_prop_sim_after_learn       3
% 3.48/0.99  --inst_sel_renew                        solver
% 3.48/0.99  --inst_lit_activity_flag                true
% 3.48/0.99  --inst_restr_to_given                   false
% 3.48/0.99  --inst_activity_threshold               500
% 3.48/0.99  --inst_out_proof                        true
% 3.48/0.99  
% 3.48/0.99  ------ Resolution Options
% 3.48/0.99  
% 3.48/0.99  --resolution_flag                       true
% 3.48/0.99  --res_lit_sel                           adaptive
% 3.48/0.99  --res_lit_sel_side                      none
% 3.48/0.99  --res_ordering                          kbo
% 3.48/0.99  --res_to_prop_solver                    active
% 3.48/0.99  --res_prop_simpl_new                    false
% 3.48/0.99  --res_prop_simpl_given                  true
% 3.48/0.99  --res_passive_queue_type                priority_queues
% 3.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/0.99  --res_passive_queues_freq               [15;5]
% 3.48/0.99  --res_forward_subs                      full
% 3.48/0.99  --res_backward_subs                     full
% 3.48/0.99  --res_forward_subs_resolution           true
% 3.48/0.99  --res_backward_subs_resolution          true
% 3.48/0.99  --res_orphan_elimination                true
% 3.48/0.99  --res_time_limit                        2.
% 3.48/0.99  --res_out_proof                         true
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Options
% 3.48/0.99  
% 3.48/0.99  --superposition_flag                    true
% 3.48/0.99  --sup_passive_queue_type                priority_queues
% 3.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.48/0.99  --demod_completeness_check              fast
% 3.48/0.99  --demod_use_ground                      true
% 3.48/0.99  --sup_to_prop_solver                    passive
% 3.48/0.99  --sup_prop_simpl_new                    true
% 3.48/0.99  --sup_prop_simpl_given                  true
% 3.48/0.99  --sup_fun_splitting                     false
% 3.48/0.99  --sup_smt_interval                      50000
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Simplification Setup
% 3.48/0.99  
% 3.48/0.99  --sup_indices_passive                   []
% 3.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_full_bw                           [BwDemod]
% 3.48/0.99  --sup_immed_triv                        [TrivRules]
% 3.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_immed_bw_main                     []
% 3.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  
% 3.48/0.99  ------ Combination Options
% 3.48/0.99  
% 3.48/0.99  --comb_res_mult                         3
% 3.48/0.99  --comb_sup_mult                         2
% 3.48/0.99  --comb_inst_mult                        10
% 3.48/0.99  
% 3.48/0.99  ------ Debug Options
% 3.48/0.99  
% 3.48/0.99  --dbg_backtrace                         false
% 3.48/0.99  --dbg_dump_prop_clauses                 false
% 3.48/0.99  --dbg_dump_prop_clauses_file            -
% 3.48/0.99  --dbg_out_stat                          false
% 3.48/0.99  ------ Parsing...
% 3.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  ------ Proving...
% 3.48/0.99  ------ Problem Properties 
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  clauses                                 19
% 3.48/0.99  conjectures                             3
% 3.48/0.99  EPR                                     0
% 3.48/0.99  Horn                                    18
% 3.48/0.99  unary                                   10
% 3.48/0.99  binary                                  5
% 3.48/0.99  lits                                    32
% 3.48/0.99  lits eq                                 16
% 3.48/0.99  fd_pure                                 0
% 3.48/0.99  fd_pseudo                               0
% 3.48/0.99  fd_cond                                 1
% 3.48/0.99  fd_pseudo_cond                          1
% 3.48/0.99  AC symbols                              0
% 3.48/0.99  
% 3.48/0.99  ------ Schedule dynamic 5 is on 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  Current options:
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options
% 3.48/0.99  
% 3.48/0.99  --out_options                           all
% 3.48/0.99  --tptp_safe_out                         true
% 3.48/0.99  --problem_path                          ""
% 3.48/0.99  --include_path                          ""
% 3.48/0.99  --clausifier                            res/vclausify_rel
% 3.48/0.99  --clausifier_options                    --mode clausify
% 3.48/0.99  --stdin                                 false
% 3.48/0.99  --stats_out                             all
% 3.48/0.99  
% 3.48/0.99  ------ General Options
% 3.48/0.99  
% 3.48/0.99  --fof                                   false
% 3.48/0.99  --time_out_real                         305.
% 3.48/0.99  --time_out_virtual                      -1.
% 3.48/0.99  --symbol_type_check                     false
% 3.48/0.99  --clausify_out                          false
% 3.48/0.99  --sig_cnt_out                           false
% 3.48/0.99  --trig_cnt_out                          false
% 3.48/0.99  --trig_cnt_out_tolerance                1.
% 3.48/0.99  --trig_cnt_out_sk_spl                   false
% 3.48/0.99  --abstr_cl_out                          false
% 3.48/0.99  
% 3.48/0.99  ------ Global Options
% 3.48/0.99  
% 3.48/0.99  --schedule                              default
% 3.48/0.99  --add_important_lit                     false
% 3.48/0.99  --prop_solver_per_cl                    1000
% 3.48/0.99  --min_unsat_core                        false
% 3.48/0.99  --soft_assumptions                      false
% 3.48/0.99  --soft_lemma_size                       3
% 3.48/0.99  --prop_impl_unit_size                   0
% 3.48/0.99  --prop_impl_unit                        []
% 3.48/0.99  --share_sel_clauses                     true
% 3.48/0.99  --reset_solvers                         false
% 3.48/0.99  --bc_imp_inh                            [conj_cone]
% 3.48/0.99  --conj_cone_tolerance                   3.
% 3.48/0.99  --extra_neg_conj                        none
% 3.48/0.99  --large_theory_mode                     true
% 3.48/0.99  --prolific_symb_bound                   200
% 3.48/0.99  --lt_threshold                          2000
% 3.48/0.99  --clause_weak_htbl                      true
% 3.48/0.99  --gc_record_bc_elim                     false
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing Options
% 3.48/0.99  
% 3.48/0.99  --preprocessing_flag                    true
% 3.48/0.99  --time_out_prep_mult                    0.1
% 3.48/0.99  --splitting_mode                        input
% 3.48/0.99  --splitting_grd                         true
% 3.48/0.99  --splitting_cvd                         false
% 3.48/0.99  --splitting_cvd_svl                     false
% 3.48/0.99  --splitting_nvd                         32
% 3.48/0.99  --sub_typing                            true
% 3.48/0.99  --prep_gs_sim                           true
% 3.48/0.99  --prep_unflatten                        true
% 3.48/0.99  --prep_res_sim                          true
% 3.48/0.99  --prep_upred                            true
% 3.48/0.99  --prep_sem_filter                       exhaustive
% 3.48/0.99  --prep_sem_filter_out                   false
% 3.48/0.99  --pred_elim                             true
% 3.48/0.99  --res_sim_input                         true
% 3.48/0.99  --eq_ax_congr_red                       true
% 3.48/0.99  --pure_diseq_elim                       true
% 3.48/0.99  --brand_transform                       false
% 3.48/0.99  --non_eq_to_eq                          false
% 3.48/0.99  --prep_def_merge                        true
% 3.48/0.99  --prep_def_merge_prop_impl              false
% 3.48/0.99  --prep_def_merge_mbd                    true
% 3.48/0.99  --prep_def_merge_tr_red                 false
% 3.48/0.99  --prep_def_merge_tr_cl                  false
% 3.48/0.99  --smt_preprocessing                     true
% 3.48/0.99  --smt_ac_axioms                         fast
% 3.48/0.99  --preprocessed_out                      false
% 3.48/0.99  --preprocessed_stats                    false
% 3.48/0.99  
% 3.48/0.99  ------ Abstraction refinement Options
% 3.48/0.99  
% 3.48/0.99  --abstr_ref                             []
% 3.48/0.99  --abstr_ref_prep                        false
% 3.48/0.99  --abstr_ref_until_sat                   false
% 3.48/0.99  --abstr_ref_sig_restrict                funpre
% 3.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/0.99  --abstr_ref_under                       []
% 3.48/0.99  
% 3.48/0.99  ------ SAT Options
% 3.48/0.99  
% 3.48/0.99  --sat_mode                              false
% 3.48/0.99  --sat_fm_restart_options                ""
% 3.48/0.99  --sat_gr_def                            false
% 3.48/0.99  --sat_epr_types                         true
% 3.48/0.99  --sat_non_cyclic_types                  false
% 3.48/0.99  --sat_finite_models                     false
% 3.48/0.99  --sat_fm_lemmas                         false
% 3.48/0.99  --sat_fm_prep                           false
% 3.48/0.99  --sat_fm_uc_incr                        true
% 3.48/0.99  --sat_out_model                         small
% 3.48/0.99  --sat_out_clauses                       false
% 3.48/0.99  
% 3.48/0.99  ------ QBF Options
% 3.48/0.99  
% 3.48/0.99  --qbf_mode                              false
% 3.48/0.99  --qbf_elim_univ                         false
% 3.48/0.99  --qbf_dom_inst                          none
% 3.48/0.99  --qbf_dom_pre_inst                      false
% 3.48/0.99  --qbf_sk_in                             false
% 3.48/0.99  --qbf_pred_elim                         true
% 3.48/0.99  --qbf_split                             512
% 3.48/0.99  
% 3.48/0.99  ------ BMC1 Options
% 3.48/0.99  
% 3.48/0.99  --bmc1_incremental                      false
% 3.48/0.99  --bmc1_axioms                           reachable_all
% 3.48/0.99  --bmc1_min_bound                        0
% 3.48/0.99  --bmc1_max_bound                        -1
% 3.48/0.99  --bmc1_max_bound_default                -1
% 3.48/0.99  --bmc1_symbol_reachability              true
% 3.48/0.99  --bmc1_property_lemmas                  false
% 3.48/0.99  --bmc1_k_induction                      false
% 3.48/0.99  --bmc1_non_equiv_states                 false
% 3.48/0.99  --bmc1_deadlock                         false
% 3.48/0.99  --bmc1_ucm                              false
% 3.48/0.99  --bmc1_add_unsat_core                   none
% 3.48/0.99  --bmc1_unsat_core_children              false
% 3.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/0.99  --bmc1_out_stat                         full
% 3.48/0.99  --bmc1_ground_init                      false
% 3.48/0.99  --bmc1_pre_inst_next_state              false
% 3.48/0.99  --bmc1_pre_inst_state                   false
% 3.48/0.99  --bmc1_pre_inst_reach_state             false
% 3.48/0.99  --bmc1_out_unsat_core                   false
% 3.48/0.99  --bmc1_aig_witness_out                  false
% 3.48/0.99  --bmc1_verbose                          false
% 3.48/0.99  --bmc1_dump_clauses_tptp                false
% 3.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.48/0.99  --bmc1_dump_file                        -
% 3.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.48/0.99  --bmc1_ucm_extend_mode                  1
% 3.48/0.99  --bmc1_ucm_init_mode                    2
% 3.48/0.99  --bmc1_ucm_cone_mode                    none
% 3.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.48/0.99  --bmc1_ucm_relax_model                  4
% 3.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/0.99  --bmc1_ucm_layered_model                none
% 3.48/0.99  --bmc1_ucm_max_lemma_size               10
% 3.48/0.99  
% 3.48/0.99  ------ AIG Options
% 3.48/0.99  
% 3.48/0.99  --aig_mode                              false
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation Options
% 3.48/0.99  
% 3.48/0.99  --instantiation_flag                    true
% 3.48/0.99  --inst_sos_flag                         false
% 3.48/0.99  --inst_sos_phase                        true
% 3.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel_side                     none
% 3.48/0.99  --inst_solver_per_active                1400
% 3.48/0.99  --inst_solver_calls_frac                1.
% 3.48/0.99  --inst_passive_queue_type               priority_queues
% 3.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/0.99  --inst_passive_queues_freq              [25;2]
% 3.48/0.99  --inst_dismatching                      true
% 3.48/0.99  --inst_eager_unprocessed_to_passive     true
% 3.48/0.99  --inst_prop_sim_given                   true
% 3.48/0.99  --inst_prop_sim_new                     false
% 3.48/0.99  --inst_subs_new                         false
% 3.48/0.99  --inst_eq_res_simp                      false
% 3.48/0.99  --inst_subs_given                       false
% 3.48/0.99  --inst_orphan_elimination               true
% 3.48/0.99  --inst_learning_loop_flag               true
% 3.48/0.99  --inst_learning_start                   3000
% 3.48/0.99  --inst_learning_factor                  2
% 3.48/0.99  --inst_start_prop_sim_after_learn       3
% 3.48/0.99  --inst_sel_renew                        solver
% 3.48/0.99  --inst_lit_activity_flag                true
% 3.48/0.99  --inst_restr_to_given                   false
% 3.48/0.99  --inst_activity_threshold               500
% 3.48/0.99  --inst_out_proof                        true
% 3.48/0.99  
% 3.48/0.99  ------ Resolution Options
% 3.48/0.99  
% 3.48/0.99  --resolution_flag                       false
% 3.48/0.99  --res_lit_sel                           adaptive
% 3.48/0.99  --res_lit_sel_side                      none
% 3.48/0.99  --res_ordering                          kbo
% 3.48/0.99  --res_to_prop_solver                    active
% 3.48/0.99  --res_prop_simpl_new                    false
% 3.48/0.99  --res_prop_simpl_given                  true
% 3.48/0.99  --res_passive_queue_type                priority_queues
% 3.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/0.99  --res_passive_queues_freq               [15;5]
% 3.48/0.99  --res_forward_subs                      full
% 3.48/0.99  --res_backward_subs                     full
% 3.48/0.99  --res_forward_subs_resolution           true
% 3.48/0.99  --res_backward_subs_resolution          true
% 3.48/0.99  --res_orphan_elimination                true
% 3.48/0.99  --res_time_limit                        2.
% 3.48/0.99  --res_out_proof                         true
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Options
% 3.48/0.99  
% 3.48/0.99  --superposition_flag                    true
% 3.48/0.99  --sup_passive_queue_type                priority_queues
% 3.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.48/0.99  --demod_completeness_check              fast
% 3.48/0.99  --demod_use_ground                      true
% 3.48/0.99  --sup_to_prop_solver                    passive
% 3.48/0.99  --sup_prop_simpl_new                    true
% 3.48/0.99  --sup_prop_simpl_given                  true
% 3.48/0.99  --sup_fun_splitting                     false
% 3.48/0.99  --sup_smt_interval                      50000
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Simplification Setup
% 3.48/0.99  
% 3.48/0.99  --sup_indices_passive                   []
% 3.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_full_bw                           [BwDemod]
% 3.48/0.99  --sup_immed_triv                        [TrivRules]
% 3.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_immed_bw_main                     []
% 3.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  
% 3.48/0.99  ------ Combination Options
% 3.48/0.99  
% 3.48/0.99  --comb_res_mult                         3
% 3.48/0.99  --comb_sup_mult                         2
% 3.48/0.99  --comb_inst_mult                        10
% 3.48/0.99  
% 3.48/0.99  ------ Debug Options
% 3.48/0.99  
% 3.48/0.99  --dbg_backtrace                         false
% 3.48/0.99  --dbg_dump_prop_clauses                 false
% 3.48/0.99  --dbg_dump_prop_clauses_file            -
% 3.48/0.99  --dbg_out_stat                          false
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  % SZS output start Saturation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  fof(f24,axiom,(
% 3.48/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f71,plain,(
% 3.48/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f24])).
% 3.48/0.99  
% 3.48/0.99  fof(f19,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f35,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f19])).
% 3.48/0.99  
% 3.48/0.99  fof(f64,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f35])).
% 3.48/0.99  
% 3.48/0.99  fof(f2,axiom,(
% 3.48/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f47,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f2])).
% 3.48/0.99  
% 3.48/0.99  fof(f25,axiom,(
% 3.48/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f72,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f25])).
% 3.48/0.99  
% 3.48/0.99  fof(f5,axiom,(
% 3.48/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f50,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f5])).
% 3.48/0.99  
% 3.48/0.99  fof(f6,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f51,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f6])).
% 3.48/0.99  
% 3.48/0.99  fof(f7,axiom,(
% 3.48/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f52,plain,(
% 3.48/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f7])).
% 3.48/0.99  
% 3.48/0.99  fof(f8,axiom,(
% 3.48/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f53,plain,(
% 3.48/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f8])).
% 3.48/0.99  
% 3.48/0.99  fof(f9,axiom,(
% 3.48/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f54,plain,(
% 3.48/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f9])).
% 3.48/0.99  
% 3.48/0.99  fof(f10,axiom,(
% 3.48/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f55,plain,(
% 3.48/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f10])).
% 3.48/0.99  
% 3.48/0.99  fof(f80,plain,(
% 3.48/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f54,f55])).
% 3.48/0.99  
% 3.48/0.99  fof(f81,plain,(
% 3.48/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f53,f80])).
% 3.48/0.99  
% 3.48/0.99  fof(f82,plain,(
% 3.48/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f52,f81])).
% 3.48/0.99  
% 3.48/0.99  fof(f83,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f51,f82])).
% 3.48/0.99  
% 3.48/0.99  fof(f84,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f50,f83])).
% 3.48/0.99  
% 3.48/0.99  fof(f85,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f72,f84])).
% 3.48/0.99  
% 3.48/0.99  fof(f86,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f47,f85])).
% 3.48/0.99  
% 3.48/0.99  fof(f95,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f64,f86])).
% 3.48/0.99  
% 3.48/0.99  fof(f16,axiom,(
% 3.48/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f61,plain,(
% 3.48/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f16])).
% 3.48/0.99  
% 3.48/0.99  fof(f20,axiom,(
% 3.48/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f65,plain,(
% 3.48/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f20])).
% 3.48/0.99  
% 3.48/0.99  fof(f14,axiom,(
% 3.48/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f59,plain,(
% 3.48/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f14])).
% 3.48/0.99  
% 3.48/0.99  fof(f89,plain,(
% 3.48/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f65,f59])).
% 3.48/0.99  
% 3.48/0.99  fof(f93,plain,(
% 3.48/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f61,f89])).
% 3.48/0.99  
% 3.48/0.99  fof(f15,axiom,(
% 3.48/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f60,plain,(
% 3.48/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f15])).
% 3.48/0.99  
% 3.48/0.99  fof(f92,plain,(
% 3.48/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.48/0.99    inference(definition_unfolding,[],[f60,f89])).
% 3.48/0.99  
% 3.48/0.99  fof(f21,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f36,plain,(
% 3.48/0.99    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f21])).
% 3.48/0.99  
% 3.48/0.99  fof(f66,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f36])).
% 3.48/0.99  
% 3.48/0.99  fof(f22,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f37,plain,(
% 3.48/0.99    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f22])).
% 3.48/0.99  
% 3.48/0.99  fof(f41,plain,(
% 3.48/0.99    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(nnf_transformation,[],[f37])).
% 3.48/0.99  
% 3.48/0.99  fof(f67,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f41])).
% 3.48/0.99  
% 3.48/0.99  fof(f97,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f67,f59])).
% 3.48/0.99  
% 3.48/0.99  fof(f23,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f38,plain,(
% 3.48/0.99    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f23])).
% 3.48/0.99  
% 3.48/0.99  fof(f42,plain,(
% 3.48/0.99    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(nnf_transformation,[],[f38])).
% 3.48/0.99  
% 3.48/0.99  fof(f69,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f42])).
% 3.48/0.99  
% 3.48/0.99  fof(f99,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k1_xboole_0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f69,f89])).
% 3.48/0.99  
% 3.48/0.99  fof(f18,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f33,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.48/0.99    inference(ennf_transformation,[],[f18])).
% 3.48/0.99  
% 3.48/0.99  fof(f34,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(flattening,[],[f33])).
% 3.48/0.99  
% 3.48/0.99  fof(f63,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f34])).
% 3.48/0.99  
% 3.48/0.99  fof(f11,axiom,(
% 3.48/0.99    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f56,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f11])).
% 3.48/0.99  
% 3.48/0.99  fof(f88,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f56,f84])).
% 3.48/0.99  
% 3.48/0.99  fof(f94,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f63,f88])).
% 3.48/0.99  
% 3.48/0.99  fof(f12,axiom,(
% 3.48/0.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f57,plain,(
% 3.48/0.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.48/0.99    inference(cnf_transformation,[],[f12])).
% 3.48/0.99  
% 3.48/0.99  fof(f4,axiom,(
% 3.48/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f49,plain,(
% 3.48/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f4])).
% 3.48/0.99  
% 3.48/0.99  fof(f87,plain,(
% 3.48/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f49,f84])).
% 3.48/0.99  
% 3.48/0.99  fof(f91,plain,(
% 3.48/0.99    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.48/0.99    inference(definition_unfolding,[],[f57,f87])).
% 3.48/0.99  
% 3.48/0.99  fof(f13,axiom,(
% 3.48/0.99    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f58,plain,(
% 3.48/0.99    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f13])).
% 3.48/0.99  
% 3.48/0.99  fof(f17,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f32,plain,(
% 3.48/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f17])).
% 3.48/0.99  
% 3.48/0.99  fof(f62,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f32])).
% 3.48/0.99  
% 3.48/0.99  fof(f68,plain,(
% 3.48/0.99    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f41])).
% 3.48/0.99  
% 3.48/0.99  fof(f96,plain,(
% 3.48/0.99    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f68,f59])).
% 3.48/0.99  
% 3.48/0.99  fof(f100,plain,(
% 3.48/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(equality_resolution,[],[f96])).
% 3.48/0.99  
% 3.48/0.99  fof(f28,conjecture,(
% 3.48/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f29,negated_conjecture,(
% 3.48/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 3.48/0.99    inference(negated_conjecture,[],[f28])).
% 3.48/0.99  
% 3.48/0.99  fof(f40,plain,(
% 3.48/0.99    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 3.48/0.99    inference(ennf_transformation,[],[f29])).
% 3.48/0.99  
% 3.48/0.99  fof(f44,plain,(
% 3.48/0.99    ( ! [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(X0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) & k2_struct_0(X0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f43,plain,(
% 3.48/0.99    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0)) => (? [X1] : (((k2_struct_0(sK0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) & k2_struct_0(sK0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f45,plain,(
% 3.48/0.99    (((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0)),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f44,f43])).
% 3.48/0.99  
% 3.48/0.99  fof(f75,plain,(
% 3.48/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.48/0.99    inference(cnf_transformation,[],[f45])).
% 3.48/0.99  
% 3.48/0.99  fof(f1,axiom,(
% 3.48/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f30,plain,(
% 3.48/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.48/0.99    inference(rectify,[],[f1])).
% 3.48/0.99  
% 3.48/0.99  fof(f46,plain,(
% 3.48/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f30])).
% 3.48/0.99  
% 3.48/0.99  fof(f90,plain,(
% 3.48/0.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.48/0.99    inference(definition_unfolding,[],[f46,f85])).
% 3.48/0.99  
% 3.48/0.99  fof(f3,axiom,(
% 3.48/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f48,plain,(
% 3.48/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f3])).
% 3.48/0.99  
% 3.48/0.99  fof(f27,axiom,(
% 3.48/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f39,plain,(
% 3.48/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 3.48/0.99    inference(ennf_transformation,[],[f27])).
% 3.48/0.99  
% 3.48/0.99  fof(f73,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f39])).
% 3.48/0.99  
% 3.48/0.99  fof(f74,plain,(
% 3.48/0.99    l1_struct_0(sK0)),
% 3.48/0.99    inference(cnf_transformation,[],[f45])).
% 3.48/0.99  
% 3.48/0.99  fof(f79,plain,(
% 3.48/0.99    k2_struct_0(sK0) = sK1 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 3.48/0.99    inference(cnf_transformation,[],[f45])).
% 3.48/0.99  
% 3.48/0.99  fof(f76,plain,(
% 3.48/0.99    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1),
% 3.48/0.99    inference(cnf_transformation,[],[f45])).
% 3.48/0.99  
% 3.48/0.99  cnf(c_203,plain,
% 3.48/0.99      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | X1 != X0 ),
% 3.48/0.99      theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_461,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_14,plain,
% 3.48/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_815,plain,
% 3.48/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.48/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_819,plain,
% 3.48/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1973,plain,
% 3.48/0.99      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k7_subset_1(X1,k1_xboole_0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_819]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2194,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(X2,k1_xboole_0,X1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1973,c_1973]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5,plain,
% 3.48/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_822,plain,
% 3.48/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4,plain,
% 3.48/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_836,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_822,c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_9,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.48/0.99      | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_818,plain,
% 3.48/0.99      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2297,plain,
% 3.48/0.99      ( k4_subset_1(X0,k3_subset_1(X0,k1_xboole_0),X1) = k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X1))
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_818]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2311,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X1)) = k4_subset_1(X0,X0,X1)
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_2297,c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2326,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_2311]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3567,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_2326]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5237,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_3567]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_11,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 3.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | k1_xboole_0 = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_817,plain,
% 3.48/0.99      ( k1_xboole_0 = X0
% 3.48/0.99      | r1_tarski(X0,k3_subset_1(X1,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5290,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X0,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_5237,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7020,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1973,c_5290]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1975,plain,
% 3.48/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_819]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7048,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_7020,c_1975]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_13,plain,
% 3.48/0.99      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
% 3.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.48/0.99      | k3_subset_1(X0,k1_xboole_0) = X1 ),
% 3.48/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_816,plain,
% 3.48/0.99      ( k3_subset_1(X0,k1_xboole_0) = X1
% 3.48/0.99      | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_868,plain,
% 3.48/0.99      ( X0 = X1
% 3.48/0.99      | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_816,c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5289,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.48/0.99      | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(X0,k1_xboole_0,X1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_5237,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6879,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.48/0.99      | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1973,c_5289]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6892,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.48/0.99      | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_6879,c_1975]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5235,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X0,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5702,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X2,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_5235]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6665,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X2,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X3,k1_xboole_0,X1))) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_5702]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5234,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.48/0.99      | r1_tarski(k4_subset_1(X1,X1,X1),k7_subset_1(X0,k1_xboole_0,X1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5680,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.48/0.99      | r1_tarski(k4_subset_1(X1,X1,X1),k7_subset_1(X2,k1_xboole_0,X1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_5234]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6633,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.48/0.99      | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(X3,k1_xboole_0,X1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_5680]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2841,plain,
% 3.48/0.99      ( k3_subset_1(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) = k4_subset_1(X0,X0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1973,c_2326]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4875,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_2841,c_1975]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4883,plain,
% 3.48/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_4875,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5523,plain,
% 3.48/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_4883]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6301,plain,
% 3.48/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0))) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_5523]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4882,plain,
% 3.48/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0
% 3.48/0.99      | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_4875,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5502,plain,
% 3.48/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0
% 3.48/0.99      | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X1,k1_xboole_0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_4882]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6265,plain,
% 3.48/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = X0
% 3.48/0.99      | r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X2,k1_xboole_0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_5502]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2844,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X0,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2326,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5365,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_2844]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5974,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0))) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_5365]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2843,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X0) = X0
% 3.48/0.99      | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X0,k1_xboole_0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2326,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5147,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X0) = X0
% 3.48/0.99      | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X1,k1_xboole_0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_2843]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5869,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,X0) = X0
% 3.48/0.99      | r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X2,k1_xboole_0,X0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3567,c_5147]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.48/0.99      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 3.48/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_820,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2405,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X1,k1_xboole_0,X0)
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_820]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3810,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_2405]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2,plain,
% 3.48/0.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3939,plain,
% 3.48/0.99      ( k4_subset_1(X0,k1_xboole_0,k1_xboole_0) = k3_tarski(k1_zfmisc_1(k1_xboole_0)) ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_3810,c_2]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3,plain,
% 3.48/0.99      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3940,plain,
% 3.48/0.99      ( k4_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_3939,c_3]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2299,plain,
% 3.48/0.99      ( k4_subset_1(X0,k3_subset_1(X0,X0),X1) = k3_subset_1(X0,k7_subset_1(X0,X0,X1))
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_818]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_821,plain,
% 3.48/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1683,plain,
% 3.48/0.99      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_821]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1691,plain,
% 3.48/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_1683,c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2302,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X0,X0,X1)) = k4_subset_1(X0,k1_xboole_0,X1)
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_2299,c_1691]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3680,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_2302]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4431,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_3940,c_3680]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4480,plain,
% 3.48/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = X0
% 3.48/0.99      | r1_tarski(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_4431,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_10,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
% 3.48/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_101,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.48/0.99      inference(global_propositional_subsumption,[status(thm)],[c_10,c_14]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_812,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_831,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_812,c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5003,plain,
% 3.48/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = X0
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4480,c_831]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2407,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X0,X0,X1)
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_820]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4421,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_2407]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_20,negated_conjecture,
% 3.48/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.48/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_814,plain,
% 3.48/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2406,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_820]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2933,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_2406]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4900,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_4421,c_2933]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3812,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_2405]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3682,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X0,X0,X0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_2302]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_0,plain,
% 3.48/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3147,plain,
% 3.48/0.99      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_0,c_1975]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1,plain,
% 3.48/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3156,plain,
% 3.48/0.99      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_3147,c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3684,plain,
% 3.48/0.99      ( k4_subset_1(X0,k1_xboole_0,X0) = X0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_3682,c_4,c_3156]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3814,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_3812,c_3684]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3811,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_2405]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4502,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = sK1 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_3814,c_3811]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3681,plain,
% 3.48/0.99      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_2302]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4635,plain,
% 3.48/0.99      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = sK1 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_4502,c_3681]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3792,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3681,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4634,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_4502,c_3792]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3791,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
% 3.48/0.99      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3681,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4633,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
% 3.48/0.99      | r1_tarski(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_4502,c_3791]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4419,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_2407]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2324,plain,
% 3.48/0.99      ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_2311]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2193,plain,
% 3.48/0.99      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_zfmisc_1(k1_xboole_0))) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2,c_1973]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1328,plain,
% 3.48/0.99      ( k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2198,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_2193,c_1328]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2199,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_2198,c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2332,plain,
% 3.48/0.99      ( k4_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_2324,c_4,c_2199]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4427,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_4419,c_2332]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2932,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_2406]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4573,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_4427,c_2932]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4481,plain,
% 3.48/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X0,X0,k1_xboole_0),k1_xboole_0) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_4431,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4420,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_2407]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2325,plain,
% 3.48/0.99      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_2311]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3570,plain,
% 3.48/0.99      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_2325]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3655,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,sK1) = u1_struct_0(sK0)
% 3.48/0.99      | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X0,k1_xboole_0,sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3570,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4083,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,sK1) = u1_struct_0(sK0)
% 3.48/0.99      | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X1,k1_xboole_0,sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_3655]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3656,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,sK1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X0,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3570,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4014,plain,
% 3.48/0.99      ( k7_subset_1(X0,k1_xboole_0,sK1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X1,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_3656]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3815,plain,
% 3.48/0.99      ( k4_subset_1(X0,k1_xboole_0,X1) = X1
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_3814,c_2405]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2866,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2325,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3569,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k7_subset_1(X0,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_2866]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2865,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = u1_struct_0(sK0)
% 3.48/0.99      | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2325,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3568,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = u1_struct_0(sK0)
% 3.48/0.99      | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X0,k1_xboole_0,sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2194,c_2865]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1974,plain,
% 3.48/0.99      ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_819]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3144,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_1975,c_1974]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2298,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0))
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_818]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3055,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_2298]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3237,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_3144,c_3055]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3053,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_2298]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3236,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_3144,c_3053]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3235,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X0))
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_3144,c_2298]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3054,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,sK1)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_2298]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2047,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_0,c_1974]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2048,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_xboole_0 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_2047,c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3059,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_3054,c_2048]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3060,plain,
% 3.48/0.99      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = u1_struct_0(sK0) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_3059,c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2934,plain,
% 3.48/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_2406]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1684,plain,
% 3.48/0.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_821]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1991,plain,
% 3.48/0.99      ( k3_subset_1(u1_struct_0(sK0),sK1) = k1_xboole_0
% 3.48/0.99      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1) != iProver_top
% 3.48/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1684,c_817]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1990,plain,
% 3.48/0.99      ( k3_subset_1(u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
% 3.48/0.99      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 3.48/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1684,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1977,plain,
% 3.48/0.99      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_1975,c_819]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1942,plain,
% 3.48/0.99      ( k1_xboole_0 = X0
% 3.48/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.48/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_4,c_868]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_27,plain,
% 3.48/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1952,plain,
% 3.48/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top | k1_xboole_0 = X0 ),
% 3.48/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1942,c_27]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1953,plain,
% 3.48/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.48/0.99      inference(renaming,[status(thm)],[c_1952]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_15,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/0.99      | ~ l1_struct_0(X1)
% 3.48/0.99      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_21,negated_conjecture,
% 3.48/0.99      ( l1_struct_0(sK0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_217,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.48/0.99      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
% 3.48/0.99      | sK0 != X1 ),
% 3.48/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_218,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.48/0.99      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
% 3.48/0.99      inference(unflattening,[status(thm)],[c_217]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_811,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 3.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1564,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_836,c_811]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_16,negated_conjecture,
% 3.48/0.99      ( k2_struct_0(sK0) = sK1
% 3.48/0.99      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_951,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_814,c_811]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_970,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
% 3.48/0.99      | k2_struct_0(sK0) = sK1 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_16,c_951]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1048,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_815,c_811]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1418,plain,
% 3.48/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
% 3.48/0.99      | k2_struct_0(sK0) = sK1 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_970,c_1048]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_19,negated_conjecture,
% 3.48/0.99      ( k2_struct_0(sK0) != sK1
% 3.48/0.99      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS output end Saturation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  ------                               Statistics
% 3.48/0.99  
% 3.48/0.99  ------ General
% 3.48/0.99  
% 3.48/0.99  abstr_ref_over_cycles:                  0
% 3.48/0.99  abstr_ref_under_cycles:                 0
% 3.48/0.99  gc_basic_clause_elim:                   0
% 3.48/0.99  forced_gc_time:                         0
% 3.48/0.99  parsing_time:                           0.01
% 3.48/0.99  unif_index_cands_time:                  0.
% 3.48/0.99  unif_index_add_time:                    0.
% 3.48/0.99  orderings_time:                         0.
% 3.48/0.99  out_proof_time:                         0.
% 3.48/0.99  total_time:                             0.269
% 3.48/0.99  num_of_symbols:                         47
% 3.48/0.99  num_of_terms:                           8129
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing
% 3.48/0.99  
% 3.48/0.99  num_of_splits:                          0
% 3.48/0.99  num_of_split_atoms:                     0
% 3.48/0.99  num_of_reused_defs:                     0
% 3.48/0.99  num_eq_ax_congr_red:                    12
% 3.48/0.99  num_of_sem_filtered_clauses:            1
% 3.48/0.99  num_of_subtypes:                        0
% 3.48/0.99  monotx_restored_types:                  0
% 3.48/0.99  sat_num_of_epr_types:                   0
% 3.48/0.99  sat_num_of_non_cyclic_types:            0
% 3.48/0.99  sat_guarded_non_collapsed_types:        0
% 3.48/0.99  num_pure_diseq_elim:                    0
% 3.48/0.99  simp_replaced_by:                       0
% 3.48/0.99  res_preprocessed:                       106
% 3.48/0.99  prep_upred:                             0
% 3.48/0.99  prep_unflattend:                        9
% 3.48/0.99  smt_new_axioms:                         0
% 3.48/0.99  pred_elim_cands:                        2
% 3.48/0.99  pred_elim:                              1
% 3.48/0.99  pred_elim_cl:                           1
% 3.48/0.99  pred_elim_cycles:                       3
% 3.48/0.99  merged_defs:                            8
% 3.48/0.99  merged_defs_ncl:                        0
% 3.48/0.99  bin_hyper_res:                          8
% 3.48/0.99  prep_cycles:                            4
% 3.48/0.99  pred_elim_time:                         0.003
% 3.48/0.99  splitting_time:                         0.
% 3.48/0.99  sem_filter_time:                        0.
% 3.48/0.99  monotx_time:                            0.001
% 3.48/0.99  subtype_inf_time:                       0.
% 3.48/0.99  
% 3.48/0.99  ------ Problem properties
% 3.48/0.99  
% 3.48/0.99  clauses:                                19
% 3.48/0.99  conjectures:                            3
% 3.48/0.99  epr:                                    0
% 3.48/0.99  horn:                                   18
% 3.48/0.99  ground:                                 4
% 3.48/0.99  unary:                                  10
% 3.48/0.99  binary:                                 5
% 3.48/0.99  lits:                                   32
% 3.48/0.99  lits_eq:                                16
% 3.48/0.99  fd_pure:                                0
% 3.48/0.99  fd_pseudo:                              0
% 3.48/0.99  fd_cond:                                1
% 3.48/0.99  fd_pseudo_cond:                         1
% 3.48/0.99  ac_symbols:                             0
% 3.48/0.99  
% 3.48/0.99  ------ Propositional Solver
% 3.48/0.99  
% 3.48/0.99  prop_solver_calls:                      29
% 3.48/0.99  prop_fast_solver_calls:                 720
% 3.48/0.99  smt_solver_calls:                       0
% 3.48/0.99  smt_fast_solver_calls:                  0
% 3.48/0.99  prop_num_of_clauses:                    2798
% 3.48/0.99  prop_preprocess_simplified:             6538
% 3.48/0.99  prop_fo_subsumed:                       4
% 3.48/0.99  prop_solver_time:                       0.
% 3.48/0.99  smt_solver_time:                        0.
% 3.48/0.99  smt_fast_solver_time:                   0.
% 3.48/0.99  prop_fast_solver_time:                  0.
% 3.48/0.99  prop_unsat_core_time:                   0.
% 3.48/0.99  
% 3.48/0.99  ------ QBF
% 3.48/0.99  
% 3.48/0.99  qbf_q_res:                              0
% 3.48/0.99  qbf_num_tautologies:                    0
% 3.48/0.99  qbf_prep_cycles:                        0
% 3.48/0.99  
% 3.48/0.99  ------ BMC1
% 3.48/0.99  
% 3.48/0.99  bmc1_current_bound:                     -1
% 3.48/0.99  bmc1_last_solved_bound:                 -1
% 3.48/0.99  bmc1_unsat_core_size:                   -1
% 3.48/0.99  bmc1_unsat_core_parents_size:           -1
% 3.48/0.99  bmc1_merge_next_fun:                    0
% 3.48/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation
% 3.48/0.99  
% 3.48/0.99  inst_num_of_clauses:                    1124
% 3.48/0.99  inst_num_in_passive:                    220
% 3.48/0.99  inst_num_in_active:                     516
% 3.48/0.99  inst_num_in_unprocessed:                388
% 3.48/0.99  inst_num_of_loops:                      570
% 3.48/0.99  inst_num_of_learning_restarts:          0
% 3.48/0.99  inst_num_moves_active_passive:          50
% 3.48/0.99  inst_lit_activity:                      0
% 3.48/0.99  inst_lit_activity_moves:                0
% 3.48/0.99  inst_num_tautologies:                   0
% 3.48/0.99  inst_num_prop_implied:                  0
% 3.48/0.99  inst_num_existing_simplified:           0
% 3.48/0.99  inst_num_eq_res_simplified:             0
% 3.48/0.99  inst_num_child_elim:                    0
% 3.48/0.99  inst_num_of_dismatching_blockings:      528
% 3.48/0.99  inst_num_of_non_proper_insts:           1033
% 3.48/0.99  inst_num_of_duplicates:                 0
% 3.48/0.99  inst_inst_num_from_inst_to_res:         0
% 3.48/0.99  inst_dismatching_checking_time:         0.
% 3.48/0.99  
% 3.48/0.99  ------ Resolution
% 3.48/0.99  
% 3.48/0.99  res_num_of_clauses:                     0
% 3.48/0.99  res_num_in_passive:                     0
% 3.48/0.99  res_num_in_active:                      0
% 3.48/0.99  res_num_of_loops:                       110
% 3.48/0.99  res_forward_subset_subsumed:            44
% 3.48/0.99  res_backward_subset_subsumed:           2
% 3.48/0.99  res_forward_subsumed:                   0
% 3.48/0.99  res_backward_subsumed:                  0
% 3.48/0.99  res_forward_subsumption_resolution:     0
% 3.48/0.99  res_backward_subsumption_resolution:    0
% 3.48/0.99  res_clause_to_clause_subsumption:       912
% 3.48/0.99  res_orphan_elimination:                 0
% 3.48/0.99  res_tautology_del:                      92
% 3.48/0.99  res_num_eq_res_simplified:              0
% 3.48/0.99  res_num_sel_changes:                    0
% 3.48/0.99  res_moves_from_active_to_pass:          0
% 3.48/0.99  
% 3.48/0.99  ------ Superposition
% 3.48/0.99  
% 3.48/0.99  sup_time_total:                         0.
% 3.48/0.99  sup_time_generating:                    0.
% 3.48/0.99  sup_time_sim_full:                      0.
% 3.48/0.99  sup_time_sim_immed:                     0.
% 3.48/0.99  
% 3.48/0.99  sup_num_of_clauses:                     107
% 3.48/0.99  sup_num_in_active:                      90
% 3.48/0.99  sup_num_in_passive:                     17
% 3.48/0.99  sup_num_of_loops:                       113
% 3.48/0.99  sup_fw_superposition:                   437
% 3.48/0.99  sup_bw_superposition:                   73
% 3.48/0.99  sup_immediate_simplified:               100
% 3.48/0.99  sup_given_eliminated:                   11
% 3.48/0.99  comparisons_done:                       0
% 3.48/0.99  comparisons_avoided:                    3
% 3.48/0.99  
% 3.48/0.99  ------ Simplifications
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  sim_fw_subset_subsumed:                 19
% 3.48/0.99  sim_bw_subset_subsumed:                 1
% 3.48/0.99  sim_fw_subsumed:                        30
% 3.48/0.99  sim_bw_subsumed:                        18
% 3.48/0.99  sim_fw_subsumption_res:                 1
% 3.48/0.99  sim_bw_subsumption_res:                 0
% 3.48/0.99  sim_tautology_del:                      1
% 3.48/0.99  sim_eq_tautology_del:                   33
% 3.48/0.99  sim_eq_res_simp:                        0
% 3.48/0.99  sim_fw_demodulated:                     65
% 3.48/0.99  sim_bw_demodulated:                     15
% 3.48/0.99  sim_light_normalised:                   31
% 3.48/0.99  sim_joinable_taut:                      0
% 3.48/0.99  sim_joinable_simp:                      0
% 3.48/0.99  sim_ac_normalised:                      0
% 3.48/0.99  sim_smt_subsumption:                    0
% 3.48/0.99  
%------------------------------------------------------------------------------

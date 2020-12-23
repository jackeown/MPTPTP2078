%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:00 EST 2020

% Result     : CounterSatisfiable 3.51s
% Output     : Saturation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  251 (6298 expanded)
%              Number of clauses        :  156 (1273 expanded)
%              Number of leaves         :   31 (1782 expanded)
%              Depth                    :   20
%              Number of atoms          :  477 (9361 expanded)
%              Number of equality atoms :  375 (7000 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f59,f57])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f25,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f81])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f82])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f83])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f84])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f64,f57])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f60,f87])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f58,f87])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f66,f57])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k1_xboole_0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f87])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f54,f82])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f44,f83])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f57])).

fof(f99,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f27,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f42,f41])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f82])).

fof(f89,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f85])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_203,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_461,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_822,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_818,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2274,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k7_subset_1(X1,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_822,c_818])).

cnf(c_3166,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(X2,k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_2274,c_2274])).

cnf(c_6,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_821,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_836,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_821,c_4])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_817,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1809,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,k1_xboole_0),X1) = k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_817])).

cnf(c_1822,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X1)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1809,c_4])).

cnf(c_1972,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_836,c_1822])).

cnf(c_3348,plain,
    ( k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_3166,c_1972])).

cnf(c_5683,plain,
    ( k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3348,c_3348])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_816,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_subset_1(X1,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5730,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5683,c_816])).

cnf(c_7081,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_5730])).

cnf(c_2276,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_836,c_818])).

cnf(c_7107,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7081,c_2276])).

cnf(c_14,plain,
    ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k1_xboole_0) = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_815,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X1
    | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_868,plain,
    ( X0 = X1
    | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_815,c_4])).

cnf(c_5729,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(X0,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5683,c_868])).

cnf(c_6938,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2274,c_5729])).

cnf(c_6950,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6938,c_2276])).

cnf(c_5681,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_816])).

cnf(c_6354,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X2,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_5681])).

cnf(c_6911,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X2,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X3,k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_6354])).

cnf(c_5680,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k4_subset_1(X1,X1,X1),k7_subset_1(X0,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_868])).

cnf(c_6160,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k4_subset_1(X1,X1,X1),k7_subset_1(X2,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_5680])).

cnf(c_6576,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = X1
    | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(X3,k1_xboole_0,X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_6160])).

cnf(c_3147,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1972,c_816])).

cnf(c_5486,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_3147])).

cnf(c_6554,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0))) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_5486])).

cnf(c_3146,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = X0
    | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1972,c_868])).

cnf(c_5337,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = X0
    | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X1,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_3146])).

cnf(c_6378,plain,
    ( k7_subset_1(X0,k1_xboole_0,X0) = X0
    | r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X2,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3348,c_5337])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_819,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2400,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X1,k1_xboole_0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_819])).

cnf(c_4712,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_822,c_2400])).

cnf(c_4714,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_836,c_2400])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3851,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2276])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3859,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3851,c_1])).

cnf(c_1811,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X0),X1) = k3_subset_1(X0,k7_subset_1(X0,X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_817])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_820,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1835,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_822,c_820])).

cnf(c_1843,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1835,c_4])).

cnf(c_3663,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,X1)) = k4_subset_1(X0,k1_xboole_0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1811,c_1843])).

cnf(c_3669,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,X0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_836,c_3663])).

cnf(c_4354,plain,
    ( k4_subset_1(X0,k1_xboole_0,X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3859,c_3669])).

cnf(c_4355,plain,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4354,c_4])).

cnf(c_4716,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4714,c_4355])).

cnf(c_4883,plain,
    ( k4_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4712,c_4716])).

cnf(c_3667,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_822,c_3663])).

cnf(c_3761,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0
    | r1_tarski(k4_subset_1(X0,k1_xboole_0,k1_xboole_0),k7_subset_1(X0,X0,k1_xboole_0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3667,c_868])).

cnf(c_5588,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0
    | r1_tarski(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4883,c_3761])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_100,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_5])).

cnf(c_812,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_831,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_812,c_4])).

cnf(c_5970,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0
    | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5588,c_831])).

cnf(c_5589,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4883,c_3667])).

cnf(c_5606,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,X0,k1_xboole_0),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5589,c_816])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_814,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4713,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_814,c_2400])).

cnf(c_4880,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_4713,c_4716])).

cnf(c_3668,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_814,c_3663])).

cnf(c_5106,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4880,c_3668])).

cnf(c_3828,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3668,c_816])).

cnf(c_5105,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4880,c_3828])).

cnf(c_3827,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3668,c_868])).

cnf(c_5104,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
    | r1_tarski(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4880,c_3827])).

cnf(c_2402,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_819])).

cnf(c_4891,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_836,c_2402])).

cnf(c_2401,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_819])).

cnf(c_2842,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_814,c_2401])).

cnf(c_5002,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_4891,c_2842])).

cnf(c_4889,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_822,c_2402])).

cnf(c_1970,plain,
    ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_822,c_1822])).

cnf(c_3167,plain,
    ( k3_subset_1(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2274,c_1970])).

cnf(c_2,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1331,plain,
    ( k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_3172,plain,
    ( k3_subset_1(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3167,c_2,c_1331])).

cnf(c_3173,plain,
    ( k4_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3172,c_1,c_4])).

cnf(c_4897,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4889,c_3173])).

cnf(c_2841,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_822,c_2401])).

cnf(c_4999,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_4897,c_2841])).

cnf(c_4890,plain,
    ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_814,c_2402])).

cnf(c_4717,plain,
    ( k4_subset_1(X0,k1_xboole_0,X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4716,c_2400])).

cnf(c_2275,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_814,c_818])).

cnf(c_3844,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_2276,c_2275])).

cnf(c_1810,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_817])).

cnf(c_3916,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3844,c_1810])).

cnf(c_3936,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_814,c_3916])).

cnf(c_2836,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_2275])).

cnf(c_2837,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2836,c_1])).

cnf(c_2036,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_814,c_1810])).

cnf(c_3064,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2837,c_2036])).

cnf(c_3065,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3064,c_4])).

cnf(c_3939,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,sK1)) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3936,c_3065])).

cnf(c_4018,plain,
    ( k7_subset_1(sK1,sK1,sK1) = u1_struct_0(sK0)
    | r1_tarski(u1_struct_0(sK0),k7_subset_1(sK1,sK1,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3939,c_868])).

cnf(c_3930,plain,
    ( k7_subset_1(sK1,sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2837,c_3844])).

cnf(c_4489,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4018,c_3930])).

cnf(c_4493,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | r1_tarski(u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4489,c_822])).

cnf(c_4094,plain,
    ( k4_subset_1(sK1,k1_xboole_0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3930,c_3669])).

cnf(c_4095,plain,
    ( k4_subset_1(sK1,k1_xboole_0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_4094,c_4])).

cnf(c_2037,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_836,c_1810])).

cnf(c_3918,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) ),
    inference(demodulation,[status(thm)],[c_3844,c_2037])).

cnf(c_2035,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_822,c_1810])).

cnf(c_3917,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_3844,c_2035])).

cnf(c_1971,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_814,c_1822])).

cnf(c_3347,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_3166,c_1971])).

cnf(c_3377,plain,
    ( k7_subset_1(X0,k1_xboole_0,sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X0,k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3347,c_868])).

cnf(c_3648,plain,
    ( k7_subset_1(X0,k1_xboole_0,sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X1,k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_3377])).

cnf(c_3378,plain,
    ( k7_subset_1(X0,k1_xboole_0,sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3347,c_816])).

cnf(c_3529,plain,
    ( k7_subset_1(X0,k1_xboole_0,sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_3378])).

cnf(c_1995,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_816])).

cnf(c_3346,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_1995])).

cnf(c_2297,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_868])).

cnf(c_3345,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = u1_struct_0(sK0)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X0,k1_xboole_0,sK1)) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_2297])).

cnf(c_3165,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_zfmisc_1(k1_xboole_0))) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_2274])).

cnf(c_3178,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3165,c_1331])).

cnf(c_3179,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3178,c_1])).

cnf(c_2843,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_836,c_2401])).

cnf(c_2294,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_868])).

cnf(c_54,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2389,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2294,c_54])).

cnf(c_2390,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2389])).

cnf(c_1836,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_814,c_820])).

cnf(c_2296,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
    | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_868])).

cnf(c_2278,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2276,c_818])).

cnf(c_1992,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_816])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

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

cnf(c_1572,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_836,c_811])).

cnf(c_16,negated_conjecture,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_951,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_814,c_811])).

cnf(c_970,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_16,c_951])).

cnf(c_1495,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_822,c_811])).

cnf(c_1497,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_970,c_1495])).

cnf(c_19,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:35:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.51/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/1.00  
% 3.51/1.00  ------  iProver source info
% 3.51/1.00  
% 3.51/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.51/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/1.00  git: non_committed_changes: false
% 3.51/1.00  git: last_make_outside_of_git: false
% 3.51/1.00  
% 3.51/1.00  ------ 
% 3.51/1.00  
% 3.51/1.00  ------ Input Options
% 3.51/1.00  
% 3.51/1.00  --out_options                           all
% 3.51/1.00  --tptp_safe_out                         true
% 3.51/1.00  --problem_path                          ""
% 3.51/1.00  --include_path                          ""
% 3.51/1.00  --clausifier                            res/vclausify_rel
% 3.51/1.00  --clausifier_options                    --mode clausify
% 3.51/1.00  --stdin                                 false
% 3.51/1.00  --stats_out                             all
% 3.51/1.00  
% 3.51/1.00  ------ General Options
% 3.51/1.00  
% 3.51/1.00  --fof                                   false
% 3.51/1.00  --time_out_real                         305.
% 3.51/1.00  --time_out_virtual                      -1.
% 3.51/1.00  --symbol_type_check                     false
% 3.51/1.00  --clausify_out                          false
% 3.51/1.00  --sig_cnt_out                           false
% 3.51/1.00  --trig_cnt_out                          false
% 3.51/1.00  --trig_cnt_out_tolerance                1.
% 3.51/1.00  --trig_cnt_out_sk_spl                   false
% 3.51/1.00  --abstr_cl_out                          false
% 3.51/1.00  
% 3.51/1.00  ------ Global Options
% 3.51/1.00  
% 3.51/1.00  --schedule                              default
% 3.51/1.00  --add_important_lit                     false
% 3.51/1.00  --prop_solver_per_cl                    1000
% 3.51/1.00  --min_unsat_core                        false
% 3.51/1.00  --soft_assumptions                      false
% 3.51/1.00  --soft_lemma_size                       3
% 3.51/1.00  --prop_impl_unit_size                   0
% 3.51/1.00  --prop_impl_unit                        []
% 3.51/1.00  --share_sel_clauses                     true
% 3.51/1.00  --reset_solvers                         false
% 3.51/1.00  --bc_imp_inh                            [conj_cone]
% 3.51/1.00  --conj_cone_tolerance                   3.
% 3.51/1.00  --extra_neg_conj                        none
% 3.51/1.00  --large_theory_mode                     true
% 3.51/1.00  --prolific_symb_bound                   200
% 3.51/1.00  --lt_threshold                          2000
% 3.51/1.00  --clause_weak_htbl                      true
% 3.51/1.00  --gc_record_bc_elim                     false
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing Options
% 3.51/1.00  
% 3.51/1.00  --preprocessing_flag                    true
% 3.51/1.00  --time_out_prep_mult                    0.1
% 3.51/1.00  --splitting_mode                        input
% 3.51/1.00  --splitting_grd                         true
% 3.51/1.00  --splitting_cvd                         false
% 3.51/1.00  --splitting_cvd_svl                     false
% 3.51/1.00  --splitting_nvd                         32
% 3.51/1.00  --sub_typing                            true
% 3.51/1.00  --prep_gs_sim                           true
% 3.51/1.00  --prep_unflatten                        true
% 3.51/1.00  --prep_res_sim                          true
% 3.51/1.00  --prep_upred                            true
% 3.51/1.00  --prep_sem_filter                       exhaustive
% 3.51/1.00  --prep_sem_filter_out                   false
% 3.51/1.00  --pred_elim                             true
% 3.51/1.00  --res_sim_input                         true
% 3.51/1.00  --eq_ax_congr_red                       true
% 3.51/1.00  --pure_diseq_elim                       true
% 3.51/1.00  --brand_transform                       false
% 3.51/1.00  --non_eq_to_eq                          false
% 3.51/1.00  --prep_def_merge                        true
% 3.51/1.00  --prep_def_merge_prop_impl              false
% 3.51/1.00  --prep_def_merge_mbd                    true
% 3.51/1.00  --prep_def_merge_tr_red                 false
% 3.51/1.00  --prep_def_merge_tr_cl                  false
% 3.51/1.00  --smt_preprocessing                     true
% 3.51/1.00  --smt_ac_axioms                         fast
% 3.51/1.00  --preprocessed_out                      false
% 3.51/1.00  --preprocessed_stats                    false
% 3.51/1.00  
% 3.51/1.00  ------ Abstraction refinement Options
% 3.51/1.00  
% 3.51/1.00  --abstr_ref                             []
% 3.51/1.00  --abstr_ref_prep                        false
% 3.51/1.00  --abstr_ref_until_sat                   false
% 3.51/1.00  --abstr_ref_sig_restrict                funpre
% 3.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/1.00  --abstr_ref_under                       []
% 3.51/1.00  
% 3.51/1.00  ------ SAT Options
% 3.51/1.00  
% 3.51/1.00  --sat_mode                              false
% 3.51/1.00  --sat_fm_restart_options                ""
% 3.51/1.00  --sat_gr_def                            false
% 3.51/1.00  --sat_epr_types                         true
% 3.51/1.00  --sat_non_cyclic_types                  false
% 3.51/1.00  --sat_finite_models                     false
% 3.51/1.00  --sat_fm_lemmas                         false
% 3.51/1.00  --sat_fm_prep                           false
% 3.51/1.00  --sat_fm_uc_incr                        true
% 3.51/1.00  --sat_out_model                         small
% 3.51/1.00  --sat_out_clauses                       false
% 3.51/1.00  
% 3.51/1.00  ------ QBF Options
% 3.51/1.00  
% 3.51/1.00  --qbf_mode                              false
% 3.51/1.00  --qbf_elim_univ                         false
% 3.51/1.00  --qbf_dom_inst                          none
% 3.51/1.00  --qbf_dom_pre_inst                      false
% 3.51/1.00  --qbf_sk_in                             false
% 3.51/1.00  --qbf_pred_elim                         true
% 3.51/1.00  --qbf_split                             512
% 3.51/1.00  
% 3.51/1.00  ------ BMC1 Options
% 3.51/1.00  
% 3.51/1.00  --bmc1_incremental                      false
% 3.51/1.00  --bmc1_axioms                           reachable_all
% 3.51/1.00  --bmc1_min_bound                        0
% 3.51/1.00  --bmc1_max_bound                        -1
% 3.51/1.00  --bmc1_max_bound_default                -1
% 3.51/1.00  --bmc1_symbol_reachability              true
% 3.51/1.00  --bmc1_property_lemmas                  false
% 3.51/1.00  --bmc1_k_induction                      false
% 3.51/1.00  --bmc1_non_equiv_states                 false
% 3.51/1.00  --bmc1_deadlock                         false
% 3.51/1.00  --bmc1_ucm                              false
% 3.51/1.00  --bmc1_add_unsat_core                   none
% 3.51/1.00  --bmc1_unsat_core_children              false
% 3.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/1.00  --bmc1_out_stat                         full
% 3.51/1.00  --bmc1_ground_init                      false
% 3.51/1.00  --bmc1_pre_inst_next_state              false
% 3.51/1.00  --bmc1_pre_inst_state                   false
% 3.51/1.00  --bmc1_pre_inst_reach_state             false
% 3.51/1.00  --bmc1_out_unsat_core                   false
% 3.51/1.00  --bmc1_aig_witness_out                  false
% 3.51/1.00  --bmc1_verbose                          false
% 3.51/1.00  --bmc1_dump_clauses_tptp                false
% 3.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.51/1.00  --bmc1_dump_file                        -
% 3.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.51/1.00  --bmc1_ucm_extend_mode                  1
% 3.51/1.00  --bmc1_ucm_init_mode                    2
% 3.51/1.00  --bmc1_ucm_cone_mode                    none
% 3.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.51/1.00  --bmc1_ucm_relax_model                  4
% 3.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/1.00  --bmc1_ucm_layered_model                none
% 3.51/1.00  --bmc1_ucm_max_lemma_size               10
% 3.51/1.00  
% 3.51/1.00  ------ AIG Options
% 3.51/1.00  
% 3.51/1.00  --aig_mode                              false
% 3.51/1.00  
% 3.51/1.00  ------ Instantiation Options
% 3.51/1.00  
% 3.51/1.00  --instantiation_flag                    true
% 3.51/1.00  --inst_sos_flag                         false
% 3.51/1.00  --inst_sos_phase                        true
% 3.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/1.00  --inst_lit_sel_side                     num_symb
% 3.51/1.00  --inst_solver_per_active                1400
% 3.51/1.00  --inst_solver_calls_frac                1.
% 3.51/1.00  --inst_passive_queue_type               priority_queues
% 3.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/1.00  --inst_passive_queues_freq              [25;2]
% 3.51/1.00  --inst_dismatching                      true
% 3.51/1.00  --inst_eager_unprocessed_to_passive     true
% 3.51/1.00  --inst_prop_sim_given                   true
% 3.51/1.00  --inst_prop_sim_new                     false
% 3.51/1.00  --inst_subs_new                         false
% 3.51/1.00  --inst_eq_res_simp                      false
% 3.51/1.00  --inst_subs_given                       false
% 3.51/1.00  --inst_orphan_elimination               true
% 3.51/1.00  --inst_learning_loop_flag               true
% 3.51/1.00  --inst_learning_start                   3000
% 3.51/1.00  --inst_learning_factor                  2
% 3.51/1.00  --inst_start_prop_sim_after_learn       3
% 3.51/1.00  --inst_sel_renew                        solver
% 3.51/1.00  --inst_lit_activity_flag                true
% 3.51/1.00  --inst_restr_to_given                   false
% 3.51/1.00  --inst_activity_threshold               500
% 3.51/1.00  --inst_out_proof                        true
% 3.51/1.00  
% 3.51/1.00  ------ Resolution Options
% 3.51/1.00  
% 3.51/1.00  --resolution_flag                       true
% 3.51/1.00  --res_lit_sel                           adaptive
% 3.51/1.00  --res_lit_sel_side                      none
% 3.51/1.00  --res_ordering                          kbo
% 3.51/1.00  --res_to_prop_solver                    active
% 3.51/1.00  --res_prop_simpl_new                    false
% 3.51/1.00  --res_prop_simpl_given                  true
% 3.51/1.00  --res_passive_queue_type                priority_queues
% 3.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/1.00  --res_passive_queues_freq               [15;5]
% 3.51/1.00  --res_forward_subs                      full
% 3.51/1.00  --res_backward_subs                     full
% 3.51/1.00  --res_forward_subs_resolution           true
% 3.51/1.00  --res_backward_subs_resolution          true
% 3.51/1.00  --res_orphan_elimination                true
% 3.51/1.00  --res_time_limit                        2.
% 3.51/1.00  --res_out_proof                         true
% 3.51/1.00  
% 3.51/1.00  ------ Superposition Options
% 3.51/1.00  
% 3.51/1.00  --superposition_flag                    true
% 3.51/1.00  --sup_passive_queue_type                priority_queues
% 3.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.51/1.00  --demod_completeness_check              fast
% 3.51/1.00  --demod_use_ground                      true
% 3.51/1.00  --sup_to_prop_solver                    passive
% 3.51/1.00  --sup_prop_simpl_new                    true
% 3.51/1.00  --sup_prop_simpl_given                  true
% 3.51/1.00  --sup_fun_splitting                     false
% 3.51/1.00  --sup_smt_interval                      50000
% 3.51/1.00  
% 3.51/1.00  ------ Superposition Simplification Setup
% 3.51/1.00  
% 3.51/1.00  --sup_indices_passive                   []
% 3.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_full_bw                           [BwDemod]
% 3.51/1.00  --sup_immed_triv                        [TrivRules]
% 3.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_immed_bw_main                     []
% 3.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/1.00  
% 3.51/1.00  ------ Combination Options
% 3.51/1.00  
% 3.51/1.00  --comb_res_mult                         3
% 3.51/1.00  --comb_sup_mult                         2
% 3.51/1.00  --comb_inst_mult                        10
% 3.51/1.00  
% 3.51/1.00  ------ Debug Options
% 3.51/1.00  
% 3.51/1.00  --dbg_backtrace                         false
% 3.51/1.00  --dbg_dump_prop_clauses                 false
% 3.51/1.00  --dbg_dump_prop_clauses_file            -
% 3.51/1.00  --dbg_out_stat                          false
% 3.51/1.00  ------ Parsing...
% 3.51/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/1.00  ------ Proving...
% 3.51/1.00  ------ Problem Properties 
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  clauses                                 19
% 3.51/1.00  conjectures                             3
% 3.51/1.00  EPR                                     0
% 3.51/1.00  Horn                                    18
% 3.51/1.00  unary                                   10
% 3.51/1.00  binary                                  5
% 3.51/1.00  lits                                    32
% 3.51/1.00  lits eq                                 16
% 3.51/1.00  fd_pure                                 0
% 3.51/1.00  fd_pseudo                               0
% 3.51/1.00  fd_cond                                 1
% 3.51/1.00  fd_pseudo_cond                          1
% 3.51/1.00  AC symbols                              0
% 3.51/1.00  
% 3.51/1.00  ------ Schedule dynamic 5 is on 
% 3.51/1.00  
% 3.51/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  ------ 
% 3.51/1.00  Current options:
% 3.51/1.00  ------ 
% 3.51/1.00  
% 3.51/1.00  ------ Input Options
% 3.51/1.00  
% 3.51/1.00  --out_options                           all
% 3.51/1.00  --tptp_safe_out                         true
% 3.51/1.00  --problem_path                          ""
% 3.51/1.00  --include_path                          ""
% 3.51/1.00  --clausifier                            res/vclausify_rel
% 3.51/1.00  --clausifier_options                    --mode clausify
% 3.51/1.00  --stdin                                 false
% 3.51/1.00  --stats_out                             all
% 3.51/1.00  
% 3.51/1.00  ------ General Options
% 3.51/1.00  
% 3.51/1.00  --fof                                   false
% 3.51/1.00  --time_out_real                         305.
% 3.51/1.00  --time_out_virtual                      -1.
% 3.51/1.00  --symbol_type_check                     false
% 3.51/1.00  --clausify_out                          false
% 3.51/1.00  --sig_cnt_out                           false
% 3.51/1.00  --trig_cnt_out                          false
% 3.51/1.00  --trig_cnt_out_tolerance                1.
% 3.51/1.00  --trig_cnt_out_sk_spl                   false
% 3.51/1.00  --abstr_cl_out                          false
% 3.51/1.00  
% 3.51/1.00  ------ Global Options
% 3.51/1.00  
% 3.51/1.00  --schedule                              default
% 3.51/1.00  --add_important_lit                     false
% 3.51/1.00  --prop_solver_per_cl                    1000
% 3.51/1.00  --min_unsat_core                        false
% 3.51/1.00  --soft_assumptions                      false
% 3.51/1.00  --soft_lemma_size                       3
% 3.51/1.00  --prop_impl_unit_size                   0
% 3.51/1.00  --prop_impl_unit                        []
% 3.51/1.00  --share_sel_clauses                     true
% 3.51/1.00  --reset_solvers                         false
% 3.51/1.00  --bc_imp_inh                            [conj_cone]
% 3.51/1.00  --conj_cone_tolerance                   3.
% 3.51/1.00  --extra_neg_conj                        none
% 3.51/1.00  --large_theory_mode                     true
% 3.51/1.00  --prolific_symb_bound                   200
% 3.51/1.00  --lt_threshold                          2000
% 3.51/1.00  --clause_weak_htbl                      true
% 3.51/1.00  --gc_record_bc_elim                     false
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing Options
% 3.51/1.00  
% 3.51/1.00  --preprocessing_flag                    true
% 3.51/1.00  --time_out_prep_mult                    0.1
% 3.51/1.00  --splitting_mode                        input
% 3.51/1.00  --splitting_grd                         true
% 3.51/1.00  --splitting_cvd                         false
% 3.51/1.00  --splitting_cvd_svl                     false
% 3.51/1.00  --splitting_nvd                         32
% 3.51/1.00  --sub_typing                            true
% 3.51/1.00  --prep_gs_sim                           true
% 3.51/1.00  --prep_unflatten                        true
% 3.51/1.00  --prep_res_sim                          true
% 3.51/1.00  --prep_upred                            true
% 3.51/1.00  --prep_sem_filter                       exhaustive
% 3.51/1.00  --prep_sem_filter_out                   false
% 3.51/1.00  --pred_elim                             true
% 3.51/1.00  --res_sim_input                         true
% 3.51/1.00  --eq_ax_congr_red                       true
% 3.51/1.00  --pure_diseq_elim                       true
% 3.51/1.00  --brand_transform                       false
% 3.51/1.00  --non_eq_to_eq                          false
% 3.51/1.00  --prep_def_merge                        true
% 3.51/1.00  --prep_def_merge_prop_impl              false
% 3.51/1.00  --prep_def_merge_mbd                    true
% 3.51/1.00  --prep_def_merge_tr_red                 false
% 3.51/1.00  --prep_def_merge_tr_cl                  false
% 3.51/1.00  --smt_preprocessing                     true
% 3.51/1.00  --smt_ac_axioms                         fast
% 3.51/1.00  --preprocessed_out                      false
% 3.51/1.00  --preprocessed_stats                    false
% 3.51/1.00  
% 3.51/1.00  ------ Abstraction refinement Options
% 3.51/1.00  
% 3.51/1.00  --abstr_ref                             []
% 3.51/1.00  --abstr_ref_prep                        false
% 3.51/1.00  --abstr_ref_until_sat                   false
% 3.51/1.00  --abstr_ref_sig_restrict                funpre
% 3.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/1.00  --abstr_ref_under                       []
% 3.51/1.00  
% 3.51/1.00  ------ SAT Options
% 3.51/1.00  
% 3.51/1.00  --sat_mode                              false
% 3.51/1.00  --sat_fm_restart_options                ""
% 3.51/1.00  --sat_gr_def                            false
% 3.51/1.00  --sat_epr_types                         true
% 3.51/1.00  --sat_non_cyclic_types                  false
% 3.51/1.00  --sat_finite_models                     false
% 3.51/1.00  --sat_fm_lemmas                         false
% 3.51/1.00  --sat_fm_prep                           false
% 3.51/1.00  --sat_fm_uc_incr                        true
% 3.51/1.00  --sat_out_model                         small
% 3.51/1.00  --sat_out_clauses                       false
% 3.51/1.00  
% 3.51/1.00  ------ QBF Options
% 3.51/1.00  
% 3.51/1.00  --qbf_mode                              false
% 3.51/1.00  --qbf_elim_univ                         false
% 3.51/1.00  --qbf_dom_inst                          none
% 3.51/1.00  --qbf_dom_pre_inst                      false
% 3.51/1.00  --qbf_sk_in                             false
% 3.51/1.00  --qbf_pred_elim                         true
% 3.51/1.00  --qbf_split                             512
% 3.51/1.00  
% 3.51/1.00  ------ BMC1 Options
% 3.51/1.00  
% 3.51/1.00  --bmc1_incremental                      false
% 3.51/1.00  --bmc1_axioms                           reachable_all
% 3.51/1.00  --bmc1_min_bound                        0
% 3.51/1.00  --bmc1_max_bound                        -1
% 3.51/1.00  --bmc1_max_bound_default                -1
% 3.51/1.00  --bmc1_symbol_reachability              true
% 3.51/1.00  --bmc1_property_lemmas                  false
% 3.51/1.00  --bmc1_k_induction                      false
% 3.51/1.00  --bmc1_non_equiv_states                 false
% 3.51/1.00  --bmc1_deadlock                         false
% 3.51/1.00  --bmc1_ucm                              false
% 3.51/1.00  --bmc1_add_unsat_core                   none
% 3.51/1.00  --bmc1_unsat_core_children              false
% 3.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/1.00  --bmc1_out_stat                         full
% 3.51/1.00  --bmc1_ground_init                      false
% 3.51/1.00  --bmc1_pre_inst_next_state              false
% 3.51/1.00  --bmc1_pre_inst_state                   false
% 3.51/1.00  --bmc1_pre_inst_reach_state             false
% 3.51/1.00  --bmc1_out_unsat_core                   false
% 3.51/1.00  --bmc1_aig_witness_out                  false
% 3.51/1.00  --bmc1_verbose                          false
% 3.51/1.00  --bmc1_dump_clauses_tptp                false
% 3.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.51/1.00  --bmc1_dump_file                        -
% 3.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.51/1.00  --bmc1_ucm_extend_mode                  1
% 3.51/1.00  --bmc1_ucm_init_mode                    2
% 3.51/1.00  --bmc1_ucm_cone_mode                    none
% 3.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.51/1.00  --bmc1_ucm_relax_model                  4
% 3.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/1.00  --bmc1_ucm_layered_model                none
% 3.51/1.00  --bmc1_ucm_max_lemma_size               10
% 3.51/1.00  
% 3.51/1.00  ------ AIG Options
% 3.51/1.00  
% 3.51/1.00  --aig_mode                              false
% 3.51/1.00  
% 3.51/1.00  ------ Instantiation Options
% 3.51/1.00  
% 3.51/1.00  --instantiation_flag                    true
% 3.51/1.00  --inst_sos_flag                         false
% 3.51/1.00  --inst_sos_phase                        true
% 3.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/1.00  --inst_lit_sel_side                     none
% 3.51/1.00  --inst_solver_per_active                1400
% 3.51/1.00  --inst_solver_calls_frac                1.
% 3.51/1.00  --inst_passive_queue_type               priority_queues
% 3.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/1.00  --inst_passive_queues_freq              [25;2]
% 3.51/1.00  --inst_dismatching                      true
% 3.51/1.00  --inst_eager_unprocessed_to_passive     true
% 3.51/1.00  --inst_prop_sim_given                   true
% 3.51/1.00  --inst_prop_sim_new                     false
% 3.51/1.00  --inst_subs_new                         false
% 3.51/1.00  --inst_eq_res_simp                      false
% 3.51/1.00  --inst_subs_given                       false
% 3.51/1.00  --inst_orphan_elimination               true
% 3.51/1.00  --inst_learning_loop_flag               true
% 3.51/1.00  --inst_learning_start                   3000
% 3.51/1.00  --inst_learning_factor                  2
% 3.51/1.00  --inst_start_prop_sim_after_learn       3
% 3.51/1.00  --inst_sel_renew                        solver
% 3.51/1.00  --inst_lit_activity_flag                true
% 3.51/1.00  --inst_restr_to_given                   false
% 3.51/1.00  --inst_activity_threshold               500
% 3.51/1.00  --inst_out_proof                        true
% 3.51/1.00  
% 3.51/1.00  ------ Resolution Options
% 3.51/1.00  
% 3.51/1.00  --resolution_flag                       false
% 3.51/1.00  --res_lit_sel                           adaptive
% 3.51/1.00  --res_lit_sel_side                      none
% 3.51/1.00  --res_ordering                          kbo
% 3.51/1.00  --res_to_prop_solver                    active
% 3.51/1.00  --res_prop_simpl_new                    false
% 3.51/1.00  --res_prop_simpl_given                  true
% 3.51/1.00  --res_passive_queue_type                priority_queues
% 3.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/1.00  --res_passive_queues_freq               [15;5]
% 3.51/1.00  --res_forward_subs                      full
% 3.51/1.00  --res_backward_subs                     full
% 3.51/1.00  --res_forward_subs_resolution           true
% 3.51/1.00  --res_backward_subs_resolution          true
% 3.51/1.00  --res_orphan_elimination                true
% 3.51/1.00  --res_time_limit                        2.
% 3.51/1.00  --res_out_proof                         true
% 3.51/1.00  
% 3.51/1.00  ------ Superposition Options
% 3.51/1.00  
% 3.51/1.00  --superposition_flag                    true
% 3.51/1.00  --sup_passive_queue_type                priority_queues
% 3.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.51/1.00  --demod_completeness_check              fast
% 3.51/1.00  --demod_use_ground                      true
% 3.51/1.00  --sup_to_prop_solver                    passive
% 3.51/1.00  --sup_prop_simpl_new                    true
% 3.51/1.00  --sup_prop_simpl_given                  true
% 3.51/1.00  --sup_fun_splitting                     false
% 3.51/1.00  --sup_smt_interval                      50000
% 3.51/1.00  
% 3.51/1.00  ------ Superposition Simplification Setup
% 3.51/1.00  
% 3.51/1.00  --sup_indices_passive                   []
% 3.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_full_bw                           [BwDemod]
% 3.51/1.00  --sup_immed_triv                        [TrivRules]
% 3.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_immed_bw_main                     []
% 3.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/1.00  
% 3.51/1.00  ------ Combination Options
% 3.51/1.00  
% 3.51/1.00  --comb_res_mult                         3
% 3.51/1.00  --comb_sup_mult                         2
% 3.51/1.00  --comb_inst_mult                        10
% 3.51/1.00  
% 3.51/1.00  ------ Debug Options
% 3.51/1.00  
% 3.51/1.00  --dbg_backtrace                         false
% 3.51/1.00  --dbg_dump_prop_clauses                 false
% 3.51/1.00  --dbg_dump_prop_clauses_file            -
% 3.51/1.00  --dbg_out_stat                          false
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  ------ Proving...
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  % SZS output start Saturation for theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  fof(f16,axiom,(
% 3.51/1.00    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f59,plain,(
% 3.51/1.00    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f16])).
% 3.51/1.00  
% 3.51/1.00  fof(f14,axiom,(
% 3.51/1.00    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f57,plain,(
% 3.51/1.00    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f14])).
% 3.51/1.00  
% 3.51/1.00  fof(f91,plain,(
% 3.51/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f59,f57])).
% 3.51/1.00  
% 3.51/1.00  fof(f20,axiom,(
% 3.51/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f33,plain,(
% 3.51/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f20])).
% 3.51/1.00  
% 3.51/1.00  fof(f63,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f33])).
% 3.51/1.00  
% 3.51/1.00  fof(f2,axiom,(
% 3.51/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f45,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f2])).
% 3.51/1.00  
% 3.51/1.00  fof(f25,axiom,(
% 3.51/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f70,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f25])).
% 3.51/1.00  
% 3.51/1.00  fof(f5,axiom,(
% 3.51/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f48,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f5])).
% 3.51/1.00  
% 3.51/1.00  fof(f6,axiom,(
% 3.51/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f49,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f6])).
% 3.51/1.00  
% 3.51/1.00  fof(f7,axiom,(
% 3.51/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f50,plain,(
% 3.51/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f7])).
% 3.51/1.00  
% 3.51/1.00  fof(f8,axiom,(
% 3.51/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f51,plain,(
% 3.51/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f8])).
% 3.51/1.00  
% 3.51/1.00  fof(f9,axiom,(
% 3.51/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f52,plain,(
% 3.51/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f9])).
% 3.51/1.00  
% 3.51/1.00  fof(f10,axiom,(
% 3.51/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f53,plain,(
% 3.51/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f10])).
% 3.51/1.00  
% 3.51/1.00  fof(f78,plain,(
% 3.51/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.51/1.00    inference(definition_unfolding,[],[f52,f53])).
% 3.51/1.00  
% 3.51/1.00  fof(f79,plain,(
% 3.51/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.51/1.00    inference(definition_unfolding,[],[f51,f78])).
% 3.51/1.00  
% 3.51/1.00  fof(f80,plain,(
% 3.51/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.51/1.00    inference(definition_unfolding,[],[f50,f79])).
% 3.51/1.00  
% 3.51/1.00  fof(f81,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.51/1.00    inference(definition_unfolding,[],[f49,f80])).
% 3.51/1.00  
% 3.51/1.00  fof(f82,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.51/1.00    inference(definition_unfolding,[],[f48,f81])).
% 3.51/1.00  
% 3.51/1.00  fof(f83,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f70,f82])).
% 3.51/1.00  
% 3.51/1.00  fof(f84,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f45,f83])).
% 3.51/1.00  
% 3.51/1.00  fof(f94,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f63,f84])).
% 3.51/1.00  
% 3.51/1.00  fof(f17,axiom,(
% 3.51/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f60,plain,(
% 3.51/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f17])).
% 3.51/1.00  
% 3.51/1.00  fof(f21,axiom,(
% 3.51/1.00    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f64,plain,(
% 3.51/1.00    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f21])).
% 3.51/1.00  
% 3.51/1.00  fof(f87,plain,(
% 3.51/1.00    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.51/1.00    inference(definition_unfolding,[],[f64,f57])).
% 3.51/1.00  
% 3.51/1.00  fof(f92,plain,(
% 3.51/1.00    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f60,f87])).
% 3.51/1.00  
% 3.51/1.00  fof(f15,axiom,(
% 3.51/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f58,plain,(
% 3.51/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.51/1.00    inference(cnf_transformation,[],[f15])).
% 3.51/1.00  
% 3.51/1.00  fof(f90,plain,(
% 3.51/1.00    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.51/1.00    inference(definition_unfolding,[],[f58,f87])).
% 3.51/1.00  
% 3.51/1.00  fof(f22,axiom,(
% 3.51/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f34,plain,(
% 3.51/1.00    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f22])).
% 3.51/1.00  
% 3.51/1.00  fof(f65,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f34])).
% 3.51/1.00  
% 3.51/1.00  fof(f23,axiom,(
% 3.51/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f35,plain,(
% 3.51/1.00    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f23])).
% 3.51/1.00  
% 3.51/1.00  fof(f39,plain,(
% 3.51/1.00    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/1.00    inference(nnf_transformation,[],[f35])).
% 3.51/1.00  
% 3.51/1.00  fof(f66,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f39])).
% 3.51/1.00  
% 3.51/1.00  fof(f96,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f66,f57])).
% 3.51/1.00  
% 3.51/1.00  fof(f24,axiom,(
% 3.51/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f36,plain,(
% 3.51/1.00    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f24])).
% 3.51/1.00  
% 3.51/1.00  fof(f40,plain,(
% 3.51/1.00    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/1.00    inference(nnf_transformation,[],[f36])).
% 3.51/1.00  
% 3.51/1.00  fof(f68,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f40])).
% 3.51/1.00  
% 3.51/1.00  fof(f98,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k1_xboole_0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f68,f87])).
% 3.51/1.00  
% 3.51/1.00  fof(f19,axiom,(
% 3.51/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f31,plain,(
% 3.51/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.51/1.00    inference(ennf_transformation,[],[f19])).
% 3.51/1.00  
% 3.51/1.00  fof(f32,plain,(
% 3.51/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/1.00    inference(flattening,[],[f31])).
% 3.51/1.00  
% 3.51/1.00  fof(f62,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f32])).
% 3.51/1.00  
% 3.51/1.00  fof(f11,axiom,(
% 3.51/1.00    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f54,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f11])).
% 3.51/1.00  
% 3.51/1.00  fof(f86,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.51/1.00    inference(definition_unfolding,[],[f54,f82])).
% 3.51/1.00  
% 3.51/1.00  fof(f93,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f62,f86])).
% 3.51/1.00  
% 3.51/1.00  fof(f1,axiom,(
% 3.51/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f29,plain,(
% 3.51/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.51/1.00    inference(rectify,[],[f1])).
% 3.51/1.00  
% 3.51/1.00  fof(f44,plain,(
% 3.51/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.51/1.00    inference(cnf_transformation,[],[f29])).
% 3.51/1.00  
% 3.51/1.00  fof(f88,plain,(
% 3.51/1.00    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.51/1.00    inference(definition_unfolding,[],[f44,f83])).
% 3.51/1.00  
% 3.51/1.00  fof(f3,axiom,(
% 3.51/1.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f46,plain,(
% 3.51/1.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.51/1.00    inference(cnf_transformation,[],[f3])).
% 3.51/1.00  
% 3.51/1.00  fof(f18,axiom,(
% 3.51/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f30,plain,(
% 3.51/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f18])).
% 3.51/1.00  
% 3.51/1.00  fof(f61,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f30])).
% 3.51/1.00  
% 3.51/1.00  fof(f67,plain,(
% 3.51/1.00    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f39])).
% 3.51/1.00  
% 3.51/1.00  fof(f95,plain,(
% 3.51/1.00    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(definition_unfolding,[],[f67,f57])).
% 3.51/1.00  
% 3.51/1.00  fof(f99,plain,(
% 3.51/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.51/1.00    inference(equality_resolution,[],[f95])).
% 3.51/1.00  
% 3.51/1.00  fof(f27,conjecture,(
% 3.51/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f28,negated_conjecture,(
% 3.51/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 3.51/1.00    inference(negated_conjecture,[],[f27])).
% 3.51/1.00  
% 3.51/1.00  fof(f38,plain,(
% 3.51/1.00    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f28])).
% 3.51/1.00  
% 3.51/1.00  fof(f42,plain,(
% 3.51/1.00    ( ! [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(X0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) & k2_struct_0(X0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f41,plain,(
% 3.51/1.00    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0)) => (? [X1] : (((k2_struct_0(sK0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) & k2_struct_0(sK0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0))),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f43,plain,(
% 3.51/1.00    (((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0)),
% 3.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f42,f41])).
% 3.51/1.00  
% 3.51/1.00  fof(f73,plain,(
% 3.51/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.51/1.00    inference(cnf_transformation,[],[f43])).
% 3.51/1.00  
% 3.51/1.00  fof(f12,axiom,(
% 3.51/1.00    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f55,plain,(
% 3.51/1.00    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.51/1.00    inference(cnf_transformation,[],[f12])).
% 3.51/1.00  
% 3.51/1.00  fof(f4,axiom,(
% 3.51/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f47,plain,(
% 3.51/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f4])).
% 3.51/1.00  
% 3.51/1.00  fof(f85,plain,(
% 3.51/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.51/1.00    inference(definition_unfolding,[],[f47,f82])).
% 3.51/1.00  
% 3.51/1.00  fof(f89,plain,(
% 3.51/1.00    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.51/1.00    inference(definition_unfolding,[],[f55,f85])).
% 3.51/1.00  
% 3.51/1.00  fof(f26,axiom,(
% 3.51/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f37,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f26])).
% 3.51/1.00  
% 3.51/1.00  fof(f71,plain,(
% 3.51/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f37])).
% 3.51/1.00  
% 3.51/1.00  fof(f72,plain,(
% 3.51/1.00    l1_struct_0(sK0)),
% 3.51/1.00    inference(cnf_transformation,[],[f43])).
% 3.51/1.00  
% 3.51/1.00  fof(f77,plain,(
% 3.51/1.00    k2_struct_0(sK0) = sK1 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 3.51/1.00    inference(cnf_transformation,[],[f43])).
% 3.51/1.00  
% 3.51/1.00  fof(f74,plain,(
% 3.51/1.00    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1),
% 3.51/1.00    inference(cnf_transformation,[],[f43])).
% 3.51/1.00  
% 3.51/1.00  fof(f13,axiom,(
% 3.51/1.00    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f56,plain,(
% 3.51/1.00    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.51/1.00    inference(cnf_transformation,[],[f13])).
% 3.51/1.00  
% 3.51/1.00  cnf(c_203,plain,
% 3.51/1.00      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | X1 != X0 ),
% 3.51/1.00      theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_461,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5,plain,
% 3.51/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.51/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_822,plain,
% 3.51/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/1.00      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.51/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_818,plain,
% 3.51/1.00      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2274,plain,
% 3.51/1.00      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k7_subset_1(X1,k1_xboole_0,X0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_818]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3166,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(X2,k1_xboole_0,X1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2274,c_2274]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6,plain,
% 3.51/1.00      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 3.51/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_821,plain,
% 3.51/1.00      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4,plain,
% 3.51/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_836,plain,
% 3.51/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_821,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.51/1.00      | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
% 3.51/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_817,plain,
% 3.51/1.00      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.51/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1809,plain,
% 3.51/1.00      ( k4_subset_1(X0,k3_subset_1(X0,k1_xboole_0),X1) = k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X1))
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_817]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1822,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X1)) = k4_subset_1(X0,X0,X1)
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_1809,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1972,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_1822]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3348,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_1972]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5683,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) = k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0)) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3348,c_3348]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_12,plain,
% 3.51/1.00      ( ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 3.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/1.00      | k1_xboole_0 = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_816,plain,
% 3.51/1.00      ( k1_xboole_0 = X0
% 3.51/1.00      | r1_tarski(X0,k3_subset_1(X1,X0)) != iProver_top
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5730,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X0,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5683,c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7081,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2274,c_5730]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2276,plain,
% 3.51/1.00      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_818]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7107,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_7081,c_2276]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_14,plain,
% 3.51/1.00      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
% 3.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.51/1.00      | k3_subset_1(X0,k1_xboole_0) = X1 ),
% 3.51/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_815,plain,
% 3.51/1.00      ( k3_subset_1(X0,k1_xboole_0) = X1
% 3.51/1.00      | r1_tarski(k3_subset_1(X0,X1),X1) != iProver_top
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_868,plain,
% 3.51/1.00      ( X0 = X1
% 3.51/1.00      | r1_tarski(k3_subset_1(X1,X0),X0) != iProver_top
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_815,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5729,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.51/1.00      | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(X0,k1_xboole_0,X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5683,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6938,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.51/1.00      | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2274,c_5729]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6950,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.51/1.00      | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_6938,c_2276]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5681,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X0,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3348,c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6354,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X2,k1_xboole_0,X1),k4_subset_1(X1,X1,X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_5681]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6911,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X2,k1_xboole_0,X1),k3_subset_1(X1,k7_subset_1(X3,k1_xboole_0,X1))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3348,c_6354]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5680,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.51/1.00      | r1_tarski(k4_subset_1(X1,X1,X1),k7_subset_1(X0,k1_xboole_0,X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3348,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6160,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.51/1.00      | r1_tarski(k4_subset_1(X1,X1,X1),k7_subset_1(X2,k1_xboole_0,X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_5680]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6576,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X1) = X1
% 3.51/1.00      | r1_tarski(k3_subset_1(X1,k7_subset_1(X2,k1_xboole_0,X1)),k7_subset_1(X3,k1_xboole_0,X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X1),k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3348,c_6160]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3147,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X0,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1972,c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5486,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k4_subset_1(X0,X0,X0)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_3147]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6554,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X0) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X1,k1_xboole_0,X0),k3_subset_1(X0,k7_subset_1(X2,k1_xboole_0,X0))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3348,c_5486]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3146,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X0) = X0
% 3.51/1.00      | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X0,k1_xboole_0,X0)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1972,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5337,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X0) = X0
% 3.51/1.00      | r1_tarski(k4_subset_1(X0,X0,X0),k7_subset_1(X1,k1_xboole_0,X0)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_3146]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6378,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,X0) = X0
% 3.51/1.00      | r1_tarski(k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)),k7_subset_1(X2,k1_xboole_0,X0)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,X0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3348,c_5337]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.51/1.00      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 3.51/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_819,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2400,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X1,k1_xboole_0,X0)
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_819]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4712,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_2400]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4714,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_2400]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_0,plain,
% 3.51/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3851,plain,
% 3.51/1.00      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_0,c_2276]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1,plain,
% 3.51/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3859,plain,
% 3.51/1.00      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3851,c_1]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1811,plain,
% 3.51/1.00      ( k4_subset_1(X0,k3_subset_1(X0,X0),X1) = k3_subset_1(X0,k7_subset_1(X0,X0,X1))
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_817]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_820,plain,
% 3.51/1.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1835,plain,
% 3.51/1.00      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_820]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1843,plain,
% 3.51/1.00      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_1835,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3663,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X0,X0,X1)) = k4_subset_1(X0,k1_xboole_0,X1)
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_1811,c_1843]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3669,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X0,X0,X0)) = k4_subset_1(X0,k1_xboole_0,X0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_3663]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4354,plain,
% 3.51/1.00      ( k4_subset_1(X0,k1_xboole_0,X0) = k3_subset_1(X0,k1_xboole_0) ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_3859,c_3669]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4355,plain,
% 3.51/1.00      ( k4_subset_1(X0,k1_xboole_0,X0) = X0 ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_4354,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4716,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_4714,c_4355]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4883,plain,
% 3.51/1.00      ( k4_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4712,c_4716]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3667,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_3663]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3761,plain,
% 3.51/1.00      ( k7_subset_1(X0,X0,k1_xboole_0) = X0
% 3.51/1.00      | r1_tarski(k4_subset_1(X0,k1_xboole_0,k1_xboole_0),k7_subset_1(X0,X0,k1_xboole_0)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3667,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5588,plain,
% 3.51/1.00      ( k7_subset_1(X0,X0,k1_xboole_0) = X0
% 3.51/1.00      | r1_tarski(k1_xboole_0,k7_subset_1(X0,X0,k1_xboole_0)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4883,c_3761]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11,plain,
% 3.51/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
% 3.51/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.51/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_100,plain,
% 3.51/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_11,c_5]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_812,plain,
% 3.51/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_100]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_831,plain,
% 3.51/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_812,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5970,plain,
% 3.51/1.00      ( k7_subset_1(X0,X0,k1_xboole_0) = X0
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5588,c_831]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5589,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4883,c_3667]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5606,plain,
% 3.51/1.00      ( k7_subset_1(X0,X0,k1_xboole_0) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X0,X0,k1_xboole_0),k1_xboole_0) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,X0,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5589,c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_20,negated_conjecture,
% 3.51/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.51/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_814,plain,
% 3.51/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4713,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_2400]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4880,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = sK1 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4713,c_4716]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3668,plain,
% 3.51/1.00      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_3663]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5106,plain,
% 3.51/1.00      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = sK1 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4880,c_3668]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3828,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3668,c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5105,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4880,c_3828]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3827,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
% 3.51/1.00      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3668,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5104,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
% 3.51/1.00      | r1_tarski(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4880,c_3827]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2402,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X0,X0,X1)
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_819]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4891,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_2402]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2401,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_819]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2842,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_2401]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5002,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4891,c_2842]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4889,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_2402]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1970,plain,
% 3.51/1.00      ( k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_1822]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3167,plain,
% 3.51/1.00      ( k3_subset_1(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) = k4_subset_1(X0,X0,k1_xboole_0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2274,c_1970]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2,plain,
% 3.51/1.00      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1331,plain,
% 3.51/1.00      ( k1_setfam_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3172,plain,
% 3.51/1.00      ( k3_subset_1(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_subset_1(X0,X0,k1_xboole_0) ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3167,c_2,c_1331]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3173,plain,
% 3.51/1.00      ( k4_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_3172,c_1,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4897,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_4889,c_3173]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2841,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_2401]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4999,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4897,c_2841]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4890,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_2402]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4717,plain,
% 3.51/1.00      ( k4_subset_1(X0,k1_xboole_0,X1) = X1
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4716,c_2400]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2275,plain,
% 3.51/1.00      ( k5_xboole_0(sK1,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_818]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3844,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_2276,c_2275]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1810,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0))
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_817]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3916,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,X0))
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_3844,c_1810]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3936,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,sK1)) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_3916]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2836,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,sK1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_0,c_2275]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2837,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k1_xboole_0 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_2836,c_1]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2036,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,sK1)) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_1810]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3064,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_2837,c_2036]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3065,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) = u1_struct_0(sK0) ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_3064,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3939,plain,
% 3.51/1.00      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,sK1)) = u1_struct_0(sK0) ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3936,c_3065]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4018,plain,
% 3.51/1.00      ( k7_subset_1(sK1,sK1,sK1) = u1_struct_0(sK0)
% 3.51/1.00      | r1_tarski(u1_struct_0(sK0),k7_subset_1(sK1,sK1,sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(sK1,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3939,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3930,plain,
% 3.51/1.00      ( k7_subset_1(sK1,sK1,sK1) = k1_xboole_0 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2837,c_3844]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4489,plain,
% 3.51/1.00      ( u1_struct_0(sK0) = k1_xboole_0
% 3.51/1.00      | r1_tarski(u1_struct_0(sK0),k1_xboole_0) != iProver_top
% 3.51/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_4018,c_3930]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4493,plain,
% 3.51/1.00      ( u1_struct_0(sK0) = k1_xboole_0
% 3.51/1.00      | r1_tarski(u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 3.51/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4489,c_822]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4094,plain,
% 3.51/1.00      ( k4_subset_1(sK1,k1_xboole_0,sK1) = k3_subset_1(sK1,k1_xboole_0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3930,c_3669]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4095,plain,
% 3.51/1.00      ( k4_subset_1(sK1,k1_xboole_0,sK1) = sK1 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4094,c_4]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2037,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_1810]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3918,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_3844,c_2037]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2035,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_1810]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3917,plain,
% 3.51/1.00      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)) ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_3844,c_2035]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1971,plain,
% 3.51/1.00      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_1822]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3347,plain,
% 3.51/1.00      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_1971]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3377,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,sK1) = u1_struct_0(sK0)
% 3.51/1.00      | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X0,k1_xboole_0,sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3347,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3648,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,sK1) = u1_struct_0(sK0)
% 3.51/1.00      | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X1,k1_xboole_0,sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_3377]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3378,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,sK1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X0,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3347,c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3529,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,sK1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X1,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(X0,k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_3378]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1995,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1971,c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3346,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k7_subset_1(X0,k1_xboole_0,sK1),k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_1995]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2297,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = u1_struct_0(sK0)
% 3.51/1.00      | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1971,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3345,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = u1_struct_0(sK0)
% 3.51/1.00      | r1_tarski(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),k7_subset_1(X0,k1_xboole_0,sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_2297]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3165,plain,
% 3.51/1.00      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k1_zfmisc_1(k1_xboole_0))) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2,c_2274]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3178,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3165,c_1331]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3179,plain,
% 3.51/1.00      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_3178,c_1]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2843,plain,
% 3.51/1.00      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_2401]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2294,plain,
% 3.51/1.00      ( k1_xboole_0 = X0
% 3.51/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.51/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_54,plain,
% 3.51/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2389,plain,
% 3.51/1.00      ( r1_tarski(X0,k1_xboole_0) != iProver_top | k1_xboole_0 = X0 ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2294,c_54]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2390,plain,
% 3.51/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_2389]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1836,plain,
% 3.51/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_820]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2296,plain,
% 3.51/1.00      ( k3_subset_1(u1_struct_0(sK0),sK1) = u1_struct_0(sK0)
% 3.51/1.00      | r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 3.51/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1836,c_868]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2278,plain,
% 3.51/1.00      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_2276,c_818]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1992,plain,
% 3.51/1.00      ( k3_subset_1(u1_struct_0(sK0),sK1) = k1_xboole_0
% 3.51/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1) != iProver_top
% 3.51/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_1836,c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_15,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ l1_struct_0(X1)
% 3.51/1.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_21,negated_conjecture,
% 3.51/1.00      ( l1_struct_0(sK0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_217,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
% 3.51/1.00      | sK0 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_218,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.51/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_217]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_811,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 3.51/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1572,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_836,c_811]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_16,negated_conjecture,
% 3.51/1.00      ( k2_struct_0(sK0) = sK1
% 3.51/1.00      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_951,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_814,c_811]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_970,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
% 3.51/1.00      | k2_struct_0(sK0) = sK1 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_16,c_951]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1495,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_822,c_811]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1497,plain,
% 3.51/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
% 3.51/1.00      | k2_struct_0(sK0) = sK1 ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_970,c_1495]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_19,negated_conjecture,
% 3.51/1.00      ( k2_struct_0(sK0) != sK1
% 3.51/1.00      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3,plain,
% 3.51/1.00      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  % SZS output end Saturation for theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  ------                               Statistics
% 3.51/1.00  
% 3.51/1.00  ------ General
% 3.51/1.00  
% 3.51/1.00  abstr_ref_over_cycles:                  0
% 3.51/1.00  abstr_ref_under_cycles:                 0
% 3.51/1.00  gc_basic_clause_elim:                   0
% 3.51/1.00  forced_gc_time:                         0
% 3.51/1.00  parsing_time:                           0.008
% 3.51/1.00  unif_index_cands_time:                  0.
% 3.51/1.00  unif_index_add_time:                    0.
% 3.51/1.00  orderings_time:                         0.
% 3.51/1.00  out_proof_time:                         0.
% 3.51/1.00  total_time:                             0.261
% 3.51/1.00  num_of_symbols:                         47
% 3.51/1.00  num_of_terms:                           7916
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing
% 3.51/1.00  
% 3.51/1.00  num_of_splits:                          0
% 3.51/1.00  num_of_split_atoms:                     0
% 3.51/1.00  num_of_reused_defs:                     0
% 3.51/1.00  num_eq_ax_congr_red:                    12
% 3.51/1.00  num_of_sem_filtered_clauses:            1
% 3.51/1.00  num_of_subtypes:                        0
% 3.51/1.00  monotx_restored_types:                  0
% 3.51/1.00  sat_num_of_epr_types:                   0
% 3.51/1.00  sat_num_of_non_cyclic_types:            0
% 3.51/1.00  sat_guarded_non_collapsed_types:        0
% 3.51/1.00  num_pure_diseq_elim:                    0
% 3.51/1.00  simp_replaced_by:                       0
% 3.51/1.00  res_preprocessed:                       106
% 3.51/1.00  prep_upred:                             0
% 3.51/1.00  prep_unflattend:                        9
% 3.51/1.00  smt_new_axioms:                         0
% 3.51/1.00  pred_elim_cands:                        2
% 3.51/1.00  pred_elim:                              1
% 3.51/1.00  pred_elim_cl:                           1
% 3.51/1.00  pred_elim_cycles:                       3
% 3.51/1.00  merged_defs:                            8
% 3.51/1.00  merged_defs_ncl:                        0
% 3.51/1.00  bin_hyper_res:                          8
% 3.51/1.00  prep_cycles:                            4
% 3.51/1.00  pred_elim_time:                         0.002
% 3.51/1.00  splitting_time:                         0.
% 3.51/1.00  sem_filter_time:                        0.
% 3.51/1.00  monotx_time:                            0.
% 3.51/1.00  subtype_inf_time:                       0.
% 3.51/1.00  
% 3.51/1.00  ------ Problem properties
% 3.51/1.00  
% 3.51/1.00  clauses:                                19
% 3.51/1.00  conjectures:                            3
% 3.51/1.00  epr:                                    0
% 3.51/1.00  horn:                                   18
% 3.51/1.00  ground:                                 4
% 3.51/1.00  unary:                                  10
% 3.51/1.00  binary:                                 5
% 3.51/1.00  lits:                                   32
% 3.51/1.00  lits_eq:                                16
% 3.51/1.00  fd_pure:                                0
% 3.51/1.00  fd_pseudo:                              0
% 3.51/1.00  fd_cond:                                1
% 3.51/1.00  fd_pseudo_cond:                         1
% 3.51/1.00  ac_symbols:                             0
% 3.51/1.00  
% 3.51/1.00  ------ Propositional Solver
% 3.51/1.00  
% 3.51/1.00  prop_solver_calls:                      29
% 3.51/1.00  prop_fast_solver_calls:                 700
% 3.51/1.00  smt_solver_calls:                       0
% 3.51/1.00  smt_fast_solver_calls:                  0
% 3.51/1.00  prop_num_of_clauses:                    2680
% 3.51/1.00  prop_preprocess_simplified:             6402
% 3.51/1.00  prop_fo_subsumed:                       3
% 3.51/1.00  prop_solver_time:                       0.
% 3.51/1.00  smt_solver_time:                        0.
% 3.51/1.00  smt_fast_solver_time:                   0.
% 3.51/1.00  prop_fast_solver_time:                  0.
% 3.51/1.00  prop_unsat_core_time:                   0.
% 3.51/1.00  
% 3.51/1.00  ------ QBF
% 3.51/1.00  
% 3.51/1.00  qbf_q_res:                              0
% 3.51/1.00  qbf_num_tautologies:                    0
% 3.51/1.00  qbf_prep_cycles:                        0
% 3.51/1.00  
% 3.51/1.00  ------ BMC1
% 3.51/1.00  
% 3.51/1.00  bmc1_current_bound:                     -1
% 3.51/1.00  bmc1_last_solved_bound:                 -1
% 3.51/1.00  bmc1_unsat_core_size:                   -1
% 3.51/1.00  bmc1_unsat_core_parents_size:           -1
% 3.51/1.00  bmc1_merge_next_fun:                    0
% 3.51/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.51/1.00  
% 3.51/1.00  ------ Instantiation
% 3.51/1.00  
% 3.51/1.00  inst_num_of_clauses:                    1101
% 3.51/1.00  inst_num_in_passive:                    216
% 3.51/1.00  inst_num_in_active:                     517
% 3.51/1.00  inst_num_in_unprocessed:                368
% 3.51/1.00  inst_num_of_loops:                      570
% 3.51/1.00  inst_num_of_learning_restarts:          0
% 3.51/1.00  inst_num_moves_active_passive:          49
% 3.51/1.00  inst_lit_activity:                      0
% 3.51/1.00  inst_lit_activity_moves:                0
% 3.51/1.00  inst_num_tautologies:                   0
% 3.51/1.00  inst_num_prop_implied:                  0
% 3.51/1.00  inst_num_existing_simplified:           0
% 3.51/1.00  inst_num_eq_res_simplified:             0
% 3.51/1.00  inst_num_child_elim:                    0
% 3.51/1.00  inst_num_of_dismatching_blockings:      522
% 3.51/1.00  inst_num_of_non_proper_insts:           1061
% 3.51/1.00  inst_num_of_duplicates:                 0
% 3.51/1.00  inst_inst_num_from_inst_to_res:         0
% 3.51/1.00  inst_dismatching_checking_time:         0.
% 3.51/1.00  
% 3.51/1.00  ------ Resolution
% 3.51/1.00  
% 3.51/1.00  res_num_of_clauses:                     0
% 3.51/1.00  res_num_in_passive:                     0
% 3.51/1.00  res_num_in_active:                      0
% 3.51/1.00  res_num_of_loops:                       110
% 3.51/1.00  res_forward_subset_subsumed:            44
% 3.51/1.00  res_backward_subset_subsumed:           2
% 3.51/1.00  res_forward_subsumed:                   0
% 3.51/1.00  res_backward_subsumed:                  0
% 3.51/1.00  res_forward_subsumption_resolution:     0
% 3.51/1.00  res_backward_subsumption_resolution:    0
% 3.51/1.00  res_clause_to_clause_subsumption:       686
% 3.51/1.00  res_orphan_elimination:                 0
% 3.51/1.00  res_tautology_del:                      123
% 3.51/1.00  res_num_eq_res_simplified:              0
% 3.51/1.00  res_num_sel_changes:                    0
% 3.51/1.00  res_moves_from_active_to_pass:          0
% 3.51/1.00  
% 3.51/1.00  ------ Superposition
% 3.51/1.00  
% 3.51/1.00  sup_time_total:                         0.
% 3.51/1.00  sup_time_generating:                    0.
% 3.51/1.00  sup_time_sim_full:                      0.
% 3.51/1.00  sup_time_sim_immed:                     0.
% 3.51/1.00  
% 3.51/1.00  sup_num_of_clauses:                     103
% 3.51/1.00  sup_num_in_active:                      88
% 3.51/1.00  sup_num_in_passive:                     15
% 3.51/1.00  sup_num_of_loops:                       113
% 3.51/1.00  sup_fw_superposition:                   332
% 3.51/1.00  sup_bw_superposition:                   80
% 3.51/1.00  sup_immediate_simplified:               83
% 3.51/1.00  sup_given_eliminated:                   8
% 3.51/1.00  comparisons_done:                       0
% 3.51/1.00  comparisons_avoided:                    3
% 3.51/1.00  
% 3.51/1.00  ------ Simplifications
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  sim_fw_subset_subsumed:                 18
% 3.51/1.00  sim_bw_subset_subsumed:                 5
% 3.51/1.00  sim_fw_subsumed:                        32
% 3.51/1.00  sim_bw_subsumed:                        6
% 3.51/1.00  sim_fw_subsumption_res:                 2
% 3.51/1.00  sim_bw_subsumption_res:                 0
% 3.51/1.00  sim_tautology_del:                      1
% 3.51/1.00  sim_eq_tautology_del:                   24
% 3.51/1.00  sim_eq_res_simp:                        0
% 3.51/1.00  sim_fw_demodulated:                     55
% 3.51/1.00  sim_bw_demodulated:                     20
% 3.51/1.00  sim_light_normalised:                   34
% 3.51/1.00  sim_joinable_taut:                      0
% 3.51/1.00  sim_joinable_simp:                      0
% 3.51/1.00  sim_ac_normalised:                      0
% 3.51/1.00  sim_smt_subsumption:                    0
% 3.51/1.00  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:10 EST 2020

% Result     : CounterSatisfiable 3.56s
% Output     : Saturation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  209 (10866 expanded)
%              Number of clauses        :  127 ( 944 expanded)
%              Number of leaves         :   27 (3444 expanded)
%              Depth                    :   18
%              Number of atoms          :  301 (13657 expanded)
%              Number of equality atoms :  218 (11346 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f81,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f71,f71])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f71])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f73,f72])).

fof(f80,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f46,f74])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f45,f73])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f42,f74,f72])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f23,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f27,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f35])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2
        & r1_xboole_0(X1,sK2)
        & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
            & r1_xboole_0(X1,X2)
            & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ? [X2] :
          ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2
          & r1_xboole_0(sK1,X2)
          & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f65,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_120,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_215,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_396,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_3])).

cnf(c_1365,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_396])).

cnf(c_4,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1367,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_396,c_4])).

cnf(c_1473,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1365,c_1367])).

cnf(c_0,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_817,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_5688,plain,
    ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1473,c_817])).

cnf(c_5691,plain,
    ( k4_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5688,c_3])).

cnf(c_804,plain,
    ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_3])).

cnf(c_5692,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5691,c_804,c_1367])).

cnf(c_1379,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_1367,c_396])).

cnf(c_803,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_4949,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1379,c_803])).

cnf(c_5737,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5692,c_4949])).

cnf(c_9,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_361,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_361,c_7])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_362,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1485,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_369,c_362])).

cnf(c_6741,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5737,c_1485])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_360,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1189,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_369,c_360])).

cnf(c_2160,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_369,c_1189])).

cnf(c_4049,plain,
    ( k4_xboole_0(k4_subset_1(X0,X0,X0),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2160,c_803])).

cnf(c_6740,plain,
    ( k4_xboole_0(k4_subset_1(X0,X0,X0),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5737,c_4049])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_358,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1187,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_358,c_360])).

cnf(c_1846,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_369,c_1187])).

cnf(c_3844,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1846,c_4])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_143,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_2])).

cnf(c_356,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_671,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_369,c_356])).

cnf(c_669,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = sK2 ),
    inference(superposition,[status(thm)],[c_358,c_356])).

cnf(c_945,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_669,c_0])).

cnf(c_1045,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2) = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_671,c_945])).

cnf(c_1051,plain,
    ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_1045,c_4])).

cnf(c_3846,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3844,c_1051])).

cnf(c_5440,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_4949,c_3846])).

cnf(c_5971,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5440,c_5692])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_357,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1188,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_360])).

cnf(c_2015,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_357,c_1188])).

cnf(c_4044,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_2160,c_2015])).

cnf(c_2687,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,sK1),sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_2015,c_803])).

cnf(c_4313,plain,
    ( k4_xboole_0(k4_subset_1(sK1,sK1,sK1),sK1) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_4044,c_2687])).

cnf(c_5438,plain,
    ( k4_xboole_0(k4_subset_1(sK1,sK1,sK1),sK1) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_4949,c_4313])).

cnf(c_5456,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_4049,c_5438])).

cnf(c_5878,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5456,c_5692])).

cnf(c_1844,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
    inference(superposition,[status(thm)],[c_358,c_1187])).

cnf(c_4043,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_2160,c_1844])).

cnf(c_1854,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,sK2),sK2) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1844,c_4])).

cnf(c_4311,plain,
    ( k4_xboole_0(k4_subset_1(sK2,sK2,sK2),sK2) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_4043,c_1854])).

cnf(c_5441,plain,
    ( k4_xboole_0(k4_subset_1(sK2,sK2,sK2),sK2) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_4949,c_4311])).

cnf(c_5753,plain,
    ( k4_xboole_0(k4_subset_1(sK2,sK2,sK2),sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5441,c_4049,c_5692])).

cnf(c_5755,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4049,c_5753])).

cnf(c_5442,plain,
    ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_4949,c_1051])).

cnf(c_5741,plain,
    ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5692,c_5442])).

cnf(c_5740,plain,
    ( k4_xboole_0(k4_subset_1(sK1,sK1,sK1),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5692,c_5438])).

cnf(c_2016,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_369,c_1188])).

cnf(c_3852,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2016,c_4])).

cnf(c_670,plain,
    ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_357,c_356])).

cnf(c_1023,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_670,c_0])).

cnf(c_1046,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_671,c_1023])).

cnf(c_1048,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_1046,c_4])).

cnf(c_3854,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3852,c_1048])).

cnf(c_5437,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_4949,c_3854])).

cnf(c_5739,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5692,c_5437])).

cnf(c_5439,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_4949,c_1048])).

cnf(c_5738,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5692,c_5439])).

cnf(c_4051,plain,
    ( k4_xboole_0(k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2160,c_396])).

cnf(c_4803,plain,
    ( k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1367,c_4051])).

cnf(c_2158,plain,
    ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_358,c_1189])).

cnf(c_2690,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_6,c_2158])).

cnf(c_3842,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_1846,c_2690])).

cnf(c_4504,plain,
    ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_3842,c_2158])).

cnf(c_4167,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2))) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_669,c_817])).

cnf(c_4177,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2))) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(light_normalisation,[status(thm)],[c_4167,c_2158])).

cnf(c_4501,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2))) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(demodulation,[status(thm)],[c_3842,c_4177])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_137,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_138,plain,
    ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_137])).

cnf(c_4166,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k1_xboole_0)),k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k1_xboole_0))) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_138,c_817])).

cnf(c_4180,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_4166,c_3,c_396])).

cnf(c_2014,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_358,c_1188])).

cnf(c_15,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2022,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2014,c_15])).

cnf(c_2540,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2022,c_803])).

cnf(c_4185,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_4180,c_2540])).

cnf(c_4168,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_670,c_817])).

cnf(c_2159,plain,
    ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_357,c_1189])).

cnf(c_2768,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_6,c_2159])).

cnf(c_3951,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2768,c_2016])).

cnf(c_3954,plain,
    ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_3951,c_2159])).

cnf(c_4174,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_4168,c_3954])).

cnf(c_3851,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_2016,c_803])).

cnf(c_3843,plain,
    ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_1846,c_803])).

cnf(c_1845,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(superposition,[status(thm)],[c_357,c_1187])).

cnf(c_2004,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(superposition,[status(thm)],[c_6,c_1845])).

cnf(c_3431,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2004,c_2022])).

cnf(c_3434,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3431,c_1845])).

cnf(c_816,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0))) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_138,c_0])).

cnf(c_822,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_816,c_3,c_4])).

cnf(c_1375,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_1367,c_822])).

cnf(c_2067,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2022,c_4])).

cnf(c_2919,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_1375,c_2067])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_359,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2447,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_369,c_359])).

cnf(c_2446,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_357,c_359])).

cnf(c_2445,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_358,c_359])).

cnf(c_1484,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_357,c_362])).

cnf(c_1483,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_358,c_362])).

cnf(c_13,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f66])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:12:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.56/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.99  
% 3.56/0.99  ------  iProver source info
% 3.56/0.99  
% 3.56/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.99  git: non_committed_changes: false
% 3.56/0.99  git: last_make_outside_of_git: false
% 3.56/0.99  
% 3.56/0.99  ------ 
% 3.56/0.99  
% 3.56/0.99  ------ Input Options
% 3.56/0.99  
% 3.56/0.99  --out_options                           all
% 3.56/0.99  --tptp_safe_out                         true
% 3.56/0.99  --problem_path                          ""
% 3.56/0.99  --include_path                          ""
% 3.56/0.99  --clausifier                            res/vclausify_rel
% 3.56/0.99  --clausifier_options                    --mode clausify
% 3.56/0.99  --stdin                                 false
% 3.56/0.99  --stats_out                             all
% 3.56/0.99  
% 3.56/0.99  ------ General Options
% 3.56/0.99  
% 3.56/0.99  --fof                                   false
% 3.56/0.99  --time_out_real                         305.
% 3.56/0.99  --time_out_virtual                      -1.
% 3.56/0.99  --symbol_type_check                     false
% 3.56/0.99  --clausify_out                          false
% 3.56/0.99  --sig_cnt_out                           false
% 3.56/0.99  --trig_cnt_out                          false
% 3.56/0.99  --trig_cnt_out_tolerance                1.
% 3.56/0.99  --trig_cnt_out_sk_spl                   false
% 3.56/0.99  --abstr_cl_out                          false
% 3.56/0.99  
% 3.56/0.99  ------ Global Options
% 3.56/0.99  
% 3.56/0.99  --schedule                              default
% 3.56/0.99  --add_important_lit                     false
% 3.56/0.99  --prop_solver_per_cl                    1000
% 3.56/0.99  --min_unsat_core                        false
% 3.56/0.99  --soft_assumptions                      false
% 3.56/0.99  --soft_lemma_size                       3
% 3.56/0.99  --prop_impl_unit_size                   0
% 3.56/0.99  --prop_impl_unit                        []
% 3.56/0.99  --share_sel_clauses                     true
% 3.56/0.99  --reset_solvers                         false
% 3.56/0.99  --bc_imp_inh                            [conj_cone]
% 3.56/0.99  --conj_cone_tolerance                   3.
% 3.56/0.99  --extra_neg_conj                        none
% 3.56/0.99  --large_theory_mode                     true
% 3.56/0.99  --prolific_symb_bound                   200
% 3.56/0.99  --lt_threshold                          2000
% 3.56/0.99  --clause_weak_htbl                      true
% 3.56/0.99  --gc_record_bc_elim                     false
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing Options
% 3.56/0.99  
% 3.56/0.99  --preprocessing_flag                    true
% 3.56/0.99  --time_out_prep_mult                    0.1
% 3.56/0.99  --splitting_mode                        input
% 3.56/0.99  --splitting_grd                         true
% 3.56/0.99  --splitting_cvd                         false
% 3.56/0.99  --splitting_cvd_svl                     false
% 3.56/0.99  --splitting_nvd                         32
% 3.56/0.99  --sub_typing                            true
% 3.56/0.99  --prep_gs_sim                           true
% 3.56/0.99  --prep_unflatten                        true
% 3.56/0.99  --prep_res_sim                          true
% 3.56/0.99  --prep_upred                            true
% 3.56/0.99  --prep_sem_filter                       exhaustive
% 3.56/0.99  --prep_sem_filter_out                   false
% 3.56/0.99  --pred_elim                             true
% 3.56/0.99  --res_sim_input                         true
% 3.56/0.99  --eq_ax_congr_red                       true
% 3.56/0.99  --pure_diseq_elim                       true
% 3.56/0.99  --brand_transform                       false
% 3.56/0.99  --non_eq_to_eq                          false
% 3.56/0.99  --prep_def_merge                        true
% 3.56/0.99  --prep_def_merge_prop_impl              false
% 3.56/0.99  --prep_def_merge_mbd                    true
% 3.56/0.99  --prep_def_merge_tr_red                 false
% 3.56/0.99  --prep_def_merge_tr_cl                  false
% 3.56/0.99  --smt_preprocessing                     true
% 3.56/0.99  --smt_ac_axioms                         fast
% 3.56/0.99  --preprocessed_out                      false
% 3.56/0.99  --preprocessed_stats                    false
% 3.56/0.99  
% 3.56/0.99  ------ Abstraction refinement Options
% 3.56/0.99  
% 3.56/0.99  --abstr_ref                             []
% 3.56/0.99  --abstr_ref_prep                        false
% 3.56/0.99  --abstr_ref_until_sat                   false
% 3.56/0.99  --abstr_ref_sig_restrict                funpre
% 3.56/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/0.99  --abstr_ref_under                       []
% 3.56/0.99  
% 3.56/0.99  ------ SAT Options
% 3.56/0.99  
% 3.56/0.99  --sat_mode                              false
% 3.56/0.99  --sat_fm_restart_options                ""
% 3.56/0.99  --sat_gr_def                            false
% 3.56/0.99  --sat_epr_types                         true
% 3.56/0.99  --sat_non_cyclic_types                  false
% 3.56/0.99  --sat_finite_models                     false
% 3.56/0.99  --sat_fm_lemmas                         false
% 3.56/0.99  --sat_fm_prep                           false
% 3.56/0.99  --sat_fm_uc_incr                        true
% 3.56/0.99  --sat_out_model                         small
% 3.56/0.99  --sat_out_clauses                       false
% 3.56/0.99  
% 3.56/0.99  ------ QBF Options
% 3.56/0.99  
% 3.56/0.99  --qbf_mode                              false
% 3.56/0.99  --qbf_elim_univ                         false
% 3.56/0.99  --qbf_dom_inst                          none
% 3.56/0.99  --qbf_dom_pre_inst                      false
% 3.56/0.99  --qbf_sk_in                             false
% 3.56/0.99  --qbf_pred_elim                         true
% 3.56/0.99  --qbf_split                             512
% 3.56/0.99  
% 3.56/0.99  ------ BMC1 Options
% 3.56/0.99  
% 3.56/0.99  --bmc1_incremental                      false
% 3.56/0.99  --bmc1_axioms                           reachable_all
% 3.56/0.99  --bmc1_min_bound                        0
% 3.56/0.99  --bmc1_max_bound                        -1
% 3.56/0.99  --bmc1_max_bound_default                -1
% 3.56/0.99  --bmc1_symbol_reachability              true
% 3.56/0.99  --bmc1_property_lemmas                  false
% 3.56/0.99  --bmc1_k_induction                      false
% 3.56/0.99  --bmc1_non_equiv_states                 false
% 3.56/0.99  --bmc1_deadlock                         false
% 3.56/0.99  --bmc1_ucm                              false
% 3.56/0.99  --bmc1_add_unsat_core                   none
% 3.56/0.99  --bmc1_unsat_core_children              false
% 3.56/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/0.99  --bmc1_out_stat                         full
% 3.56/0.99  --bmc1_ground_init                      false
% 3.56/0.99  --bmc1_pre_inst_next_state              false
% 3.56/0.99  --bmc1_pre_inst_state                   false
% 3.56/0.99  --bmc1_pre_inst_reach_state             false
% 3.56/0.99  --bmc1_out_unsat_core                   false
% 3.56/0.99  --bmc1_aig_witness_out                  false
% 3.56/0.99  --bmc1_verbose                          false
% 3.56/0.99  --bmc1_dump_clauses_tptp                false
% 3.56/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.56/0.99  --bmc1_dump_file                        -
% 3.56/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.56/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.56/0.99  --bmc1_ucm_extend_mode                  1
% 3.56/0.99  --bmc1_ucm_init_mode                    2
% 3.56/0.99  --bmc1_ucm_cone_mode                    none
% 3.56/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.56/0.99  --bmc1_ucm_relax_model                  4
% 3.56/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.56/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/0.99  --bmc1_ucm_layered_model                none
% 3.56/0.99  --bmc1_ucm_max_lemma_size               10
% 3.56/0.99  
% 3.56/0.99  ------ AIG Options
% 3.56/0.99  
% 3.56/0.99  --aig_mode                              false
% 3.56/0.99  
% 3.56/0.99  ------ Instantiation Options
% 3.56/0.99  
% 3.56/0.99  --instantiation_flag                    true
% 3.56/0.99  --inst_sos_flag                         false
% 3.56/0.99  --inst_sos_phase                        true
% 3.56/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/0.99  --inst_lit_sel_side                     num_symb
% 3.56/0.99  --inst_solver_per_active                1400
% 3.56/0.99  --inst_solver_calls_frac                1.
% 3.56/0.99  --inst_passive_queue_type               priority_queues
% 3.56/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/0.99  --inst_passive_queues_freq              [25;2]
% 3.56/0.99  --inst_dismatching                      true
% 3.56/0.99  --inst_eager_unprocessed_to_passive     true
% 3.56/0.99  --inst_prop_sim_given                   true
% 3.56/0.99  --inst_prop_sim_new                     false
% 3.56/0.99  --inst_subs_new                         false
% 3.56/0.99  --inst_eq_res_simp                      false
% 3.56/0.99  --inst_subs_given                       false
% 3.56/0.99  --inst_orphan_elimination               true
% 3.56/0.99  --inst_learning_loop_flag               true
% 3.56/0.99  --inst_learning_start                   3000
% 3.56/0.99  --inst_learning_factor                  2
% 3.56/0.99  --inst_start_prop_sim_after_learn       3
% 3.56/0.99  --inst_sel_renew                        solver
% 3.56/0.99  --inst_lit_activity_flag                true
% 3.56/0.99  --inst_restr_to_given                   false
% 3.56/0.99  --inst_activity_threshold               500
% 3.56/0.99  --inst_out_proof                        true
% 3.56/0.99  
% 3.56/0.99  ------ Resolution Options
% 3.56/0.99  
% 3.56/0.99  --resolution_flag                       true
% 3.56/0.99  --res_lit_sel                           adaptive
% 3.56/0.99  --res_lit_sel_side                      none
% 3.56/0.99  --res_ordering                          kbo
% 3.56/0.99  --res_to_prop_solver                    active
% 3.56/0.99  --res_prop_simpl_new                    false
% 3.56/0.99  --res_prop_simpl_given                  true
% 3.56/0.99  --res_passive_queue_type                priority_queues
% 3.56/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/0.99  --res_passive_queues_freq               [15;5]
% 3.56/0.99  --res_forward_subs                      full
% 3.56/0.99  --res_backward_subs                     full
% 3.56/0.99  --res_forward_subs_resolution           true
% 3.56/0.99  --res_backward_subs_resolution          true
% 3.56/0.99  --res_orphan_elimination                true
% 3.56/0.99  --res_time_limit                        2.
% 3.56/0.99  --res_out_proof                         true
% 3.56/0.99  
% 3.56/0.99  ------ Superposition Options
% 3.56/0.99  
% 3.56/0.99  --superposition_flag                    true
% 3.56/0.99  --sup_passive_queue_type                priority_queues
% 3.56/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.56/0.99  --demod_completeness_check              fast
% 3.56/0.99  --demod_use_ground                      true
% 3.56/0.99  --sup_to_prop_solver                    passive
% 3.56/0.99  --sup_prop_simpl_new                    true
% 3.56/0.99  --sup_prop_simpl_given                  true
% 3.56/0.99  --sup_fun_splitting                     false
% 3.56/0.99  --sup_smt_interval                      50000
% 3.56/0.99  
% 3.56/0.99  ------ Superposition Simplification Setup
% 3.56/0.99  
% 3.56/0.99  --sup_indices_passive                   []
% 3.56/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.99  --sup_full_bw                           [BwDemod]
% 3.56/0.99  --sup_immed_triv                        [TrivRules]
% 3.56/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.99  --sup_immed_bw_main                     []
% 3.56/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.99  
% 3.56/0.99  ------ Combination Options
% 3.56/0.99  
% 3.56/0.99  --comb_res_mult                         3
% 3.56/0.99  --comb_sup_mult                         2
% 3.56/0.99  --comb_inst_mult                        10
% 3.56/0.99  
% 3.56/0.99  ------ Debug Options
% 3.56/0.99  
% 3.56/0.99  --dbg_backtrace                         false
% 3.56/0.99  --dbg_dump_prop_clauses                 false
% 3.56/0.99  --dbg_dump_prop_clauses_file            -
% 3.56/0.99  --dbg_out_stat                          false
% 3.56/0.99  ------ Parsing...
% 3.56/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.99  ------ Proving...
% 3.56/0.99  ------ Problem Properties 
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  clauses                                 16
% 3.56/0.99  conjectures                             4
% 3.56/0.99  EPR                                     0
% 3.56/0.99  Horn                                    16
% 3.56/0.99  unary                                   12
% 3.56/0.99  binary                                  3
% 3.56/0.99  lits                                    21
% 3.56/0.99  lits eq                                 13
% 3.56/0.99  fd_pure                                 0
% 3.56/0.99  fd_pseudo                               0
% 3.56/0.99  fd_cond                                 0
% 3.56/0.99  fd_pseudo_cond                          0
% 3.56/0.99  AC symbols                              0
% 3.56/0.99  
% 3.56/0.99  ------ Schedule dynamic 5 is on 
% 3.56/0.99  
% 3.56/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ 
% 3.56/0.99  Current options:
% 3.56/0.99  ------ 
% 3.56/0.99  
% 3.56/0.99  ------ Input Options
% 3.56/0.99  
% 3.56/0.99  --out_options                           all
% 3.56/0.99  --tptp_safe_out                         true
% 3.56/0.99  --problem_path                          ""
% 3.56/0.99  --include_path                          ""
% 3.56/0.99  --clausifier                            res/vclausify_rel
% 3.56/0.99  --clausifier_options                    --mode clausify
% 3.56/0.99  --stdin                                 false
% 3.56/0.99  --stats_out                             all
% 3.56/0.99  
% 3.56/0.99  ------ General Options
% 3.56/0.99  
% 3.56/0.99  --fof                                   false
% 3.56/0.99  --time_out_real                         305.
% 3.56/0.99  --time_out_virtual                      -1.
% 3.56/0.99  --symbol_type_check                     false
% 3.56/0.99  --clausify_out                          false
% 3.56/0.99  --sig_cnt_out                           false
% 3.56/0.99  --trig_cnt_out                          false
% 3.56/0.99  --trig_cnt_out_tolerance                1.
% 3.56/0.99  --trig_cnt_out_sk_spl                   false
% 3.56/0.99  --abstr_cl_out                          false
% 3.56/0.99  
% 3.56/0.99  ------ Global Options
% 3.56/0.99  
% 3.56/0.99  --schedule                              default
% 3.56/0.99  --add_important_lit                     false
% 3.56/0.99  --prop_solver_per_cl                    1000
% 3.56/0.99  --min_unsat_core                        false
% 3.56/0.99  --soft_assumptions                      false
% 3.56/0.99  --soft_lemma_size                       3
% 3.56/0.99  --prop_impl_unit_size                   0
% 3.56/0.99  --prop_impl_unit                        []
% 3.56/0.99  --share_sel_clauses                     true
% 3.56/0.99  --reset_solvers                         false
% 3.56/0.99  --bc_imp_inh                            [conj_cone]
% 3.56/0.99  --conj_cone_tolerance                   3.
% 3.56/0.99  --extra_neg_conj                        none
% 3.56/0.99  --large_theory_mode                     true
% 3.56/0.99  --prolific_symb_bound                   200
% 3.56/0.99  --lt_threshold                          2000
% 3.56/0.99  --clause_weak_htbl                      true
% 3.56/0.99  --gc_record_bc_elim                     false
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing Options
% 3.56/0.99  
% 3.56/0.99  --preprocessing_flag                    true
% 3.56/0.99  --time_out_prep_mult                    0.1
% 3.56/0.99  --splitting_mode                        input
% 3.56/0.99  --splitting_grd                         true
% 3.56/0.99  --splitting_cvd                         false
% 3.56/0.99  --splitting_cvd_svl                     false
% 3.56/0.99  --splitting_nvd                         32
% 3.56/0.99  --sub_typing                            true
% 3.56/0.99  --prep_gs_sim                           true
% 3.56/0.99  --prep_unflatten                        true
% 3.56/0.99  --prep_res_sim                          true
% 3.56/0.99  --prep_upred                            true
% 3.56/0.99  --prep_sem_filter                       exhaustive
% 3.56/0.99  --prep_sem_filter_out                   false
% 3.56/0.99  --pred_elim                             true
% 3.56/0.99  --res_sim_input                         true
% 3.56/0.99  --eq_ax_congr_red                       true
% 3.56/0.99  --pure_diseq_elim                       true
% 3.56/0.99  --brand_transform                       false
% 3.56/0.99  --non_eq_to_eq                          false
% 3.56/0.99  --prep_def_merge                        true
% 3.56/0.99  --prep_def_merge_prop_impl              false
% 3.56/0.99  --prep_def_merge_mbd                    true
% 3.56/0.99  --prep_def_merge_tr_red                 false
% 3.56/0.99  --prep_def_merge_tr_cl                  false
% 3.56/0.99  --smt_preprocessing                     true
% 3.56/0.99  --smt_ac_axioms                         fast
% 3.56/0.99  --preprocessed_out                      false
% 3.56/0.99  --preprocessed_stats                    false
% 3.56/0.99  
% 3.56/0.99  ------ Abstraction refinement Options
% 3.56/0.99  
% 3.56/0.99  --abstr_ref                             []
% 3.56/0.99  --abstr_ref_prep                        false
% 3.56/0.99  --abstr_ref_until_sat                   false
% 3.56/0.99  --abstr_ref_sig_restrict                funpre
% 3.56/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/0.99  --abstr_ref_under                       []
% 3.56/0.99  
% 3.56/0.99  ------ SAT Options
% 3.56/0.99  
% 3.56/0.99  --sat_mode                              false
% 3.56/0.99  --sat_fm_restart_options                ""
% 3.56/0.99  --sat_gr_def                            false
% 3.56/0.99  --sat_epr_types                         true
% 3.56/0.99  --sat_non_cyclic_types                  false
% 3.56/0.99  --sat_finite_models                     false
% 3.56/0.99  --sat_fm_lemmas                         false
% 3.56/0.99  --sat_fm_prep                           false
% 3.56/0.99  --sat_fm_uc_incr                        true
% 3.56/0.99  --sat_out_model                         small
% 3.56/0.99  --sat_out_clauses                       false
% 3.56/0.99  
% 3.56/0.99  ------ QBF Options
% 3.56/0.99  
% 3.56/0.99  --qbf_mode                              false
% 3.56/0.99  --qbf_elim_univ                         false
% 3.56/0.99  --qbf_dom_inst                          none
% 3.56/0.99  --qbf_dom_pre_inst                      false
% 3.56/0.99  --qbf_sk_in                             false
% 3.56/0.99  --qbf_pred_elim                         true
% 3.56/0.99  --qbf_split                             512
% 3.56/0.99  
% 3.56/0.99  ------ BMC1 Options
% 3.56/0.99  
% 3.56/0.99  --bmc1_incremental                      false
% 3.56/0.99  --bmc1_axioms                           reachable_all
% 3.56/0.99  --bmc1_min_bound                        0
% 3.56/0.99  --bmc1_max_bound                        -1
% 3.56/0.99  --bmc1_max_bound_default                -1
% 3.56/0.99  --bmc1_symbol_reachability              true
% 3.56/0.99  --bmc1_property_lemmas                  false
% 3.56/0.99  --bmc1_k_induction                      false
% 3.56/0.99  --bmc1_non_equiv_states                 false
% 3.56/0.99  --bmc1_deadlock                         false
% 3.56/0.99  --bmc1_ucm                              false
% 3.56/0.99  --bmc1_add_unsat_core                   none
% 3.56/0.99  --bmc1_unsat_core_children              false
% 3.56/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/0.99  --bmc1_out_stat                         full
% 3.56/0.99  --bmc1_ground_init                      false
% 3.56/0.99  --bmc1_pre_inst_next_state              false
% 3.56/0.99  --bmc1_pre_inst_state                   false
% 3.56/0.99  --bmc1_pre_inst_reach_state             false
% 3.56/0.99  --bmc1_out_unsat_core                   false
% 3.56/0.99  --bmc1_aig_witness_out                  false
% 3.56/0.99  --bmc1_verbose                          false
% 3.56/0.99  --bmc1_dump_clauses_tptp                false
% 3.56/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.56/0.99  --bmc1_dump_file                        -
% 3.56/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.56/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.56/0.99  --bmc1_ucm_extend_mode                  1
% 3.56/0.99  --bmc1_ucm_init_mode                    2
% 3.56/0.99  --bmc1_ucm_cone_mode                    none
% 3.56/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.56/0.99  --bmc1_ucm_relax_model                  4
% 3.56/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.56/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/0.99  --bmc1_ucm_layered_model                none
% 3.56/0.99  --bmc1_ucm_max_lemma_size               10
% 3.56/0.99  
% 3.56/0.99  ------ AIG Options
% 3.56/0.99  
% 3.56/0.99  --aig_mode                              false
% 3.56/0.99  
% 3.56/0.99  ------ Instantiation Options
% 3.56/0.99  
% 3.56/0.99  --instantiation_flag                    true
% 3.56/0.99  --inst_sos_flag                         false
% 3.56/0.99  --inst_sos_phase                        true
% 3.56/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/0.99  --inst_lit_sel_side                     none
% 3.56/0.99  --inst_solver_per_active                1400
% 3.56/0.99  --inst_solver_calls_frac                1.
% 3.56/0.99  --inst_passive_queue_type               priority_queues
% 3.56/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/0.99  --inst_passive_queues_freq              [25;2]
% 3.56/0.99  --inst_dismatching                      true
% 3.56/0.99  --inst_eager_unprocessed_to_passive     true
% 3.56/0.99  --inst_prop_sim_given                   true
% 3.56/0.99  --inst_prop_sim_new                     false
% 3.56/0.99  --inst_subs_new                         false
% 3.56/0.99  --inst_eq_res_simp                      false
% 3.56/0.99  --inst_subs_given                       false
% 3.56/0.99  --inst_orphan_elimination               true
% 3.56/0.99  --inst_learning_loop_flag               true
% 3.56/0.99  --inst_learning_start                   3000
% 3.56/0.99  --inst_learning_factor                  2
% 3.56/0.99  --inst_start_prop_sim_after_learn       3
% 3.56/0.99  --inst_sel_renew                        solver
% 3.56/0.99  --inst_lit_activity_flag                true
% 3.56/0.99  --inst_restr_to_given                   false
% 3.56/0.99  --inst_activity_threshold               500
% 3.56/0.99  --inst_out_proof                        true
% 3.56/0.99  
% 3.56/0.99  ------ Resolution Options
% 3.56/0.99  
% 3.56/0.99  --resolution_flag                       false
% 3.56/0.99  --res_lit_sel                           adaptive
% 3.56/0.99  --res_lit_sel_side                      none
% 3.56/0.99  --res_ordering                          kbo
% 3.56/0.99  --res_to_prop_solver                    active
% 3.56/0.99  --res_prop_simpl_new                    false
% 3.56/0.99  --res_prop_simpl_given                  true
% 3.56/0.99  --res_passive_queue_type                priority_queues
% 3.56/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/0.99  --res_passive_queues_freq               [15;5]
% 3.56/0.99  --res_forward_subs                      full
% 3.56/0.99  --res_backward_subs                     full
% 3.56/0.99  --res_forward_subs_resolution           true
% 3.56/0.99  --res_backward_subs_resolution          true
% 3.56/0.99  --res_orphan_elimination                true
% 3.56/0.99  --res_time_limit                        2.
% 3.56/0.99  --res_out_proof                         true
% 3.56/0.99  
% 3.56/0.99  ------ Superposition Options
% 3.56/0.99  
% 3.56/0.99  --superposition_flag                    true
% 3.56/0.99  --sup_passive_queue_type                priority_queues
% 3.56/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.56/0.99  --demod_completeness_check              fast
% 3.56/0.99  --demod_use_ground                      true
% 3.56/0.99  --sup_to_prop_solver                    passive
% 3.56/0.99  --sup_prop_simpl_new                    true
% 3.56/0.99  --sup_prop_simpl_given                  true
% 3.56/0.99  --sup_fun_splitting                     false
% 3.56/0.99  --sup_smt_interval                      50000
% 3.56/0.99  
% 3.56/0.99  ------ Superposition Simplification Setup
% 3.56/0.99  
% 3.56/0.99  --sup_indices_passive                   []
% 3.56/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.99  --sup_full_bw                           [BwDemod]
% 3.56/0.99  --sup_immed_triv                        [TrivRules]
% 3.56/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.99  --sup_immed_bw_main                     []
% 3.56/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.99  
% 3.56/0.99  ------ Combination Options
% 3.56/0.99  
% 3.56/0.99  --comb_res_mult                         3
% 3.56/0.99  --comb_sup_mult                         2
% 3.56/0.99  --comb_inst_mult                        10
% 3.56/0.99  
% 3.56/0.99  ------ Debug Options
% 3.56/0.99  
% 3.56/0.99  --dbg_backtrace                         false
% 3.56/0.99  --dbg_dump_prop_clauses                 false
% 3.56/0.99  --dbg_dump_prop_clauses_file            -
% 3.56/0.99  --dbg_out_stat                          false
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ Proving...
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  % SZS output start Saturation for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  fof(f8,axiom,(
% 3.56/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f47,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f8])).
% 3.56/0.99  
% 3.56/0.99  fof(f9,axiom,(
% 3.56/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f48,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f9])).
% 3.56/0.99  
% 3.56/0.99  fof(f10,axiom,(
% 3.56/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f49,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f10])).
% 3.56/0.99  
% 3.56/0.99  fof(f11,axiom,(
% 3.56/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f50,plain,(
% 3.56/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f11])).
% 3.56/0.99  
% 3.56/0.99  fof(f12,axiom,(
% 3.56/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f51,plain,(
% 3.56/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f12])).
% 3.56/0.99  
% 3.56/0.99  fof(f13,axiom,(
% 3.56/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f52,plain,(
% 3.56/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f13])).
% 3.56/0.99  
% 3.56/0.99  fof(f14,axiom,(
% 3.56/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f53,plain,(
% 3.56/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f14])).
% 3.56/0.99  
% 3.56/0.99  fof(f67,plain,(
% 3.56/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f52,f53])).
% 3.56/0.99  
% 3.56/0.99  fof(f68,plain,(
% 3.56/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f51,f67])).
% 3.56/0.99  
% 3.56/0.99  fof(f69,plain,(
% 3.56/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f50,f68])).
% 3.56/0.99  
% 3.56/0.99  fof(f70,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f49,f69])).
% 3.56/0.99  
% 3.56/0.99  fof(f71,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f48,f70])).
% 3.56/0.99  
% 3.56/0.99  fof(f81,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f47,f71,f71])).
% 3.56/0.99  
% 3.56/0.99  fof(f7,axiom,(
% 3.56/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f46,plain,(
% 3.56/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.56/0.99    inference(cnf_transformation,[],[f7])).
% 3.56/0.99  
% 3.56/0.99  fof(f2,axiom,(
% 3.56/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f41,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f2])).
% 3.56/0.99  
% 3.56/0.99  fof(f15,axiom,(
% 3.56/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f54,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f15])).
% 3.56/0.99  
% 3.56/0.99  fof(f73,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f54,f71])).
% 3.56/0.99  
% 3.56/0.99  fof(f21,axiom,(
% 3.56/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f60,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f21])).
% 3.56/0.99  
% 3.56/0.99  fof(f72,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f60,f71])).
% 3.56/0.99  
% 3.56/0.99  fof(f74,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f41,f73,f72])).
% 3.56/0.99  
% 3.56/0.99  fof(f80,plain,(
% 3.56/0.99    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0) )),
% 3.56/0.99    inference(definition_unfolding,[],[f46,f74])).
% 3.56/0.99  
% 3.56/0.99  fof(f5,axiom,(
% 3.56/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f44,plain,(
% 3.56/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.56/0.99    inference(cnf_transformation,[],[f5])).
% 3.56/0.99  
% 3.56/0.99  fof(f78,plain,(
% 3.56/0.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f44,f72])).
% 3.56/0.99  
% 3.56/0.99  fof(f6,axiom,(
% 3.56/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f45,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f6])).
% 3.56/0.99  
% 3.56/0.99  fof(f79,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f45,f73])).
% 3.56/0.99  
% 3.56/0.99  fof(f3,axiom,(
% 3.56/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f42,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f3])).
% 3.56/0.99  
% 3.56/0.99  fof(f75,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f42,f74,f72])).
% 3.56/0.99  
% 3.56/0.99  fof(f18,axiom,(
% 3.56/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f57,plain,(
% 3.56/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f18])).
% 3.56/0.99  
% 3.56/0.99  fof(f16,axiom,(
% 3.56/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f55,plain,(
% 3.56/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.56/0.99    inference(cnf_transformation,[],[f16])).
% 3.56/0.99  
% 3.56/0.99  fof(f17,axiom,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f30,plain,(
% 3.56/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.99    inference(ennf_transformation,[],[f17])).
% 3.56/0.99  
% 3.56/0.99  fof(f56,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f30])).
% 3.56/0.99  
% 3.56/0.99  fof(f19,axiom,(
% 3.56/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f31,plain,(
% 3.56/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.56/0.99    inference(ennf_transformation,[],[f19])).
% 3.56/0.99  
% 3.56/0.99  fof(f32,plain,(
% 3.56/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.99    inference(flattening,[],[f31])).
% 3.56/0.99  
% 3.56/0.99  fof(f58,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f32])).
% 3.56/0.99  
% 3.56/0.99  fof(f82,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.99    inference(definition_unfolding,[],[f58,f73])).
% 3.56/0.99  
% 3.56/0.99  fof(f23,conjecture,(
% 3.56/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f24,negated_conjecture,(
% 3.56/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 3.56/0.99    inference(negated_conjecture,[],[f23])).
% 3.56/0.99  
% 3.56/0.99  fof(f27,plain,(
% 3.56/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 3.56/0.99    inference(pure_predicate_removal,[],[f24])).
% 3.56/0.99  
% 3.56/0.99  fof(f35,plain,(
% 3.56/0.99    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 3.56/0.99    inference(ennf_transformation,[],[f27])).
% 3.56/0.99  
% 3.56/0.99  fof(f36,plain,(
% 3.56/0.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 3.56/0.99    inference(flattening,[],[f35])).
% 3.56/0.99  
% 3.56/0.99  fof(f38,plain,(
% 3.56/0.99    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f37,plain,(
% 3.56/0.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f39,plain,(
% 3.56/0.99    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).
% 3.56/0.99  
% 3.56/0.99  fof(f63,plain,(
% 3.56/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.56/0.99    inference(cnf_transformation,[],[f39])).
% 3.56/0.99  
% 3.56/0.99  fof(f22,axiom,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f25,plain,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.56/0.99    inference(unused_predicate_definition_removal,[],[f22])).
% 3.56/0.99  
% 3.56/0.99  fof(f34,plain,(
% 3.56/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.56/0.99    inference(ennf_transformation,[],[f25])).
% 3.56/0.99  
% 3.56/0.99  fof(f61,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f34])).
% 3.56/0.99  
% 3.56/0.99  fof(f4,axiom,(
% 3.56/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f29,plain,(
% 3.56/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.56/0.99    inference(ennf_transformation,[],[f4])).
% 3.56/0.99  
% 3.56/0.99  fof(f43,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f29])).
% 3.56/0.99  
% 3.56/0.99  fof(f77,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f43,f72])).
% 3.56/0.99  
% 3.56/0.99  fof(f62,plain,(
% 3.56/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.56/0.99    inference(cnf_transformation,[],[f39])).
% 3.56/0.99  
% 3.56/0.99  fof(f1,axiom,(
% 3.56/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f26,plain,(
% 3.56/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.56/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.56/0.99  
% 3.56/0.99  fof(f28,plain,(
% 3.56/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.56/0.99    inference(ennf_transformation,[],[f26])).
% 3.56/0.99  
% 3.56/0.99  fof(f40,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f28])).
% 3.56/0.99  
% 3.56/0.99  fof(f76,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.56/0.99    inference(definition_unfolding,[],[f40,f72])).
% 3.56/0.99  
% 3.56/0.99  fof(f65,plain,(
% 3.56/0.99    r1_xboole_0(sK1,sK2)),
% 3.56/0.99    inference(cnf_transformation,[],[f39])).
% 3.56/0.99  
% 3.56/0.99  fof(f64,plain,(
% 3.56/0.99    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 3.56/0.99    inference(cnf_transformation,[],[f39])).
% 3.56/0.99  
% 3.56/0.99  fof(f20,axiom,(
% 3.56/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f33,plain,(
% 3.56/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.99    inference(ennf_transformation,[],[f20])).
% 3.56/0.99  
% 3.56/0.99  fof(f59,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f33])).
% 3.56/0.99  
% 3.56/0.99  fof(f66,plain,(
% 3.56/0.99    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 3.56/0.99    inference(cnf_transformation,[],[f39])).
% 3.56/0.99  
% 3.56/0.99  cnf(c_120,plain,
% 3.56/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.56/0.99      theory(equality) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_215,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_6,plain,
% 3.56/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3,plain,
% 3.56/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_396,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_xboole_0) = X0 ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_5,c_3]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1365,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)),k1_xboole_0) = X0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_6,c_396]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
% 3.56/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1367,plain,
% 3.56/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_396,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1473,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1365,c_1367]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_0,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k4_xboole_0(X0,X1) ),
% 3.56/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_817,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) = k4_xboole_0(X0,X1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5688,plain,
% 3.56/0.99      ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))))) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1473,c_817]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5691,plain,
% 3.56/0.99      ( k4_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_5688,c_3]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_804,plain,
% 3.56/0.99      ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_6,c_3]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5692,plain,
% 3.56/0.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5691,c_804,c_1367]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1379,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1367,c_396]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_803,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4949,plain,
% 3.56/0.99      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1379,c_803]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5737,plain,
% 3.56/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5692,c_4949]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_9,plain,
% 3.56/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.56/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_361,plain,
% 3.56/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_7,plain,
% 3.56/0.99      ( k2_subset_1(X0) = X0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_369,plain,
% 3.56/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_361,c_7]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_8,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_362,plain,
% 3.56/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.56/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1485,plain,
% 3.56/0.99      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_369,c_362]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_6741,plain,
% 3.56/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5737,c_1485]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_10,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.56/0.99      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 3.56/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_360,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.56/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.56/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1189,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X0,X0,X1)
% 3.56/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_369,c_360]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2160,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_369,c_1189]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4049,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(X0,X0,X0),X0) = k4_xboole_0(X0,X0) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_2160,c_803]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_6740,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(X0,X0,X0),X0) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5737,c_4049]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_16,negated_conjecture,
% 3.56/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.56/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_358,plain,
% 3.56/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1187,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.56/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_358,c_360]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1846,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_369,c_1187]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3844,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1846,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_12,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.56/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1)
% 3.56/0.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_143,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 3.56/0.99      inference(resolution,[status(thm)],[c_12,c_2]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_356,plain,
% 3.56/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 3.56/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_671,plain,
% 3.56/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_369,c_356]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_669,plain,
% 3.56/0.99      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = sK2 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_358,c_356]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_945,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_669,c_0]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1045,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK2) = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_671,c_945]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1051,plain,
% 3.56/0.99      ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k4_xboole_0(sK2,sK2) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_1045,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3846,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(sK2,sK2) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_3844,c_1051]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5440,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4949,c_3846]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5971,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5440,c_5692]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_17,negated_conjecture,
% 3.56/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.56/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_357,plain,
% 3.56/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1188,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.56/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_357,c_360]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2015,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_357,c_1188]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4044,plain,
% 3.56/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_2160,c_2015]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2687,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,sK1),sK1) = k4_xboole_0(sK1,sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_2015,c_803]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4313,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(sK1,sK1,sK1),sK1) = k4_xboole_0(sK1,sK1) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4044,c_2687]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5438,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(sK1,sK1,sK1),sK1) = k4_xboole_0(k1_xboole_0,sK1) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4949,c_4313]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5456,plain,
% 3.56/0.99      ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_4049,c_5438]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5878,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5456,c_5692]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1844,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_358,c_1187]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4043,plain,
% 3.56/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_2160,c_1844]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1854,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,sK2),sK2) = k4_xboole_0(sK2,sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1844,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4311,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(sK2,sK2,sK2),sK2) = k4_xboole_0(sK2,sK2) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4043,c_1854]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5441,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(sK2,sK2,sK2),sK2) = k4_xboole_0(k1_xboole_0,sK2) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4949,c_4311]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5753,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(sK2,sK2,sK2),sK2) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5441,c_4049,c_5692]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5755,plain,
% 3.56/0.99      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_4049,c_5753]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5442,plain,
% 3.56/0.99      ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4949,c_1051]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5741,plain,
% 3.56/0.99      ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5692,c_5442]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5740,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(sK1,sK1,sK1),sK1) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5692,c_5438]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2016,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_369,c_1188]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3852,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_2016,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_670,plain,
% 3.56/0.99      ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = sK1 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_357,c_356]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1023,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_670,c_0]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1046,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_671,c_1023]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1048,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k4_xboole_0(sK1,sK1) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_1046,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3854,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(sK1,sK1) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_3852,c_1048]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5437,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k4_xboole_0(k1_xboole_0,sK1) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4949,c_3854]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5739,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5692,c_5437]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5439,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k4_xboole_0(k1_xboole_0,sK1) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4949,c_1048]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5738,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_5692,c_5439]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4051,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_2160,c_396]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4803,plain,
% 3.56/0.99      ( k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1367,c_4051]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2158,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_358,c_1189]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2690,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_6,c_2158]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3842,plain,
% 3.56/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_1846,c_2690]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4504,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_3842,c_2158]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4167,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2))) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_669,c_817]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4177,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2))) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_4167,c_2158]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4501,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2))) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_3842,c_4177]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1,plain,
% 3.56/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.56/0.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_14,negated_conjecture,
% 3.56/0.99      ( r1_xboole_0(sK1,sK2) ),
% 3.56/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_137,plain,
% 3.56/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0
% 3.56/0.99      | sK2 != X1
% 3.56/0.99      | sK1 != X0 ),
% 3.56/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_138,plain,
% 3.56/0.99      ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k1_xboole_0 ),
% 3.56/0.99      inference(unflattening,[status(thm)],[c_137]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4166,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k1_xboole_0)),k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k1_xboole_0))) = k4_xboole_0(sK2,sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_138,c_817]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4180,plain,
% 3.56/0.99      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4166,c_3,c_396]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2014,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_358,c_1188]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_15,negated_conjecture,
% 3.56/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2022,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k2_struct_0(sK0) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_2014,c_15]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2540,plain,
% 3.56/0.99      ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_2022,c_803]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4185,plain,
% 3.56/0.99      ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_4180,c_2540]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4168,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_670,c_817]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2159,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_357,c_1189]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2768,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_6,c_2159]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3951,plain,
% 3.56/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_2768,c_2016]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3954,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_3951,c_2159]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4174,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_4168,c_3954]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3851,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_2016,c_803]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3843,plain,
% 3.56/0.99      ( k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1846,c_803]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1845,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_357,c_1187]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2004,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_6,c_1845]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3431,plain,
% 3.56/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_2004,c_2022]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3434,plain,
% 3.56/0.99      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k2_struct_0(sK0) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_3431,c_1845]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_816,plain,
% 3.56/0.99      ( k4_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0))) = k4_xboole_0(sK1,sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_138,c_0]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_822,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_816,c_3,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1375,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_1367,c_822]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2067,plain,
% 3.56/0.99      ( k4_xboole_0(k2_struct_0(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_2022,c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2919,plain,
% 3.56/0.99      ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_1375,c_2067]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_11,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.56/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_359,plain,
% 3.56/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.56/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2447,plain,
% 3.56/0.99      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_369,c_359]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2446,plain,
% 3.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_357,c_359]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2445,plain,
% 3.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_358,c_359]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1484,plain,
% 3.56/0.99      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_357,c_362]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1483,plain,
% 3.56/0.99      ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_358,c_362]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_13,negated_conjecture,
% 3.56/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 3.56/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  % SZS output end Saturation for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  ------                               Statistics
% 3.56/0.99  
% 3.56/0.99  ------ General
% 3.56/0.99  
% 3.56/0.99  abstr_ref_over_cycles:                  0
% 3.56/0.99  abstr_ref_under_cycles:                 0
% 3.56/0.99  gc_basic_clause_elim:                   0
% 3.56/0.99  forced_gc_time:                         0
% 3.56/0.99  parsing_time:                           0.01
% 3.56/0.99  unif_index_cands_time:                  0.
% 3.56/0.99  unif_index_add_time:                    0.
% 3.56/0.99  orderings_time:                         0.
% 3.56/0.99  out_proof_time:                         0.
% 3.56/0.99  total_time:                             0.409
% 3.56/0.99  num_of_symbols:                         49
% 3.56/0.99  num_of_terms:                           6129
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing
% 3.56/0.99  
% 3.56/0.99  num_of_splits:                          0
% 3.56/0.99  num_of_split_atoms:                     0
% 3.56/0.99  num_of_reused_defs:                     0
% 3.56/0.99  num_eq_ax_congr_red:                    18
% 3.56/0.99  num_of_sem_filtered_clauses:            1
% 3.56/0.99  num_of_subtypes:                        0
% 3.56/0.99  monotx_restored_types:                  0
% 3.56/0.99  sat_num_of_epr_types:                   0
% 3.56/0.99  sat_num_of_non_cyclic_types:            0
% 3.56/0.99  sat_guarded_non_collapsed_types:        0
% 3.56/0.99  num_pure_diseq_elim:                    0
% 3.56/0.99  simp_replaced_by:                       0
% 3.56/0.99  res_preprocessed:                       91
% 3.56/0.99  prep_upred:                             0
% 3.56/0.99  prep_unflattend:                        2
% 3.56/0.99  smt_new_axioms:                         0
% 3.56/0.99  pred_elim_cands:                        1
% 3.56/0.99  pred_elim:                              2
% 3.56/0.99  pred_elim_cl:                           2
% 3.56/0.99  pred_elim_cycles:                       4
% 3.56/0.99  merged_defs:                            0
% 3.56/0.99  merged_defs_ncl:                        0
% 3.56/0.99  bin_hyper_res:                          0
% 3.56/0.99  prep_cycles:                            4
% 3.56/0.99  pred_elim_time:                         0.001
% 3.56/0.99  splitting_time:                         0.
% 3.56/0.99  sem_filter_time:                        0.
% 3.56/0.99  monotx_time:                            0.
% 3.56/0.99  subtype_inf_time:                       0.
% 3.56/0.99  
% 3.56/0.99  ------ Problem properties
% 3.56/0.99  
% 3.56/0.99  clauses:                                16
% 3.56/0.99  conjectures:                            4
% 3.56/0.99  epr:                                    0
% 3.56/0.99  horn:                                   16
% 3.56/0.99  ground:                                 5
% 3.56/0.99  unary:                                  12
% 3.56/0.99  binary:                                 3
% 3.56/0.99  lits:                                   21
% 3.56/0.99  lits_eq:                                13
% 3.56/0.99  fd_pure:                                0
% 3.56/0.99  fd_pseudo:                              0
% 3.56/0.99  fd_cond:                                0
% 3.56/0.99  fd_pseudo_cond:                         0
% 3.56/0.99  ac_symbols:                             0
% 3.56/0.99  
% 3.56/0.99  ------ Propositional Solver
% 3.56/0.99  
% 3.56/0.99  prop_solver_calls:                      29
% 3.56/0.99  prop_fast_solver_calls:                 449
% 3.56/0.99  smt_solver_calls:                       0
% 3.56/0.99  smt_fast_solver_calls:                  0
% 3.56/0.99  prop_num_of_clauses:                    2761
% 3.56/0.99  prop_preprocess_simplified:             6889
% 3.56/0.99  prop_fo_subsumed:                       0
% 3.56/0.99  prop_solver_time:                       0.
% 3.56/0.99  smt_solver_time:                        0.
% 3.56/0.99  smt_fast_solver_time:                   0.
% 3.56/0.99  prop_fast_solver_time:                  0.
% 3.56/0.99  prop_unsat_core_time:                   0.
% 3.56/0.99  
% 3.56/0.99  ------ QBF
% 3.56/0.99  
% 3.56/0.99  qbf_q_res:                              0
% 3.56/0.99  qbf_num_tautologies:                    0
% 3.56/0.99  qbf_prep_cycles:                        0
% 3.56/0.99  
% 3.56/0.99  ------ BMC1
% 3.56/0.99  
% 3.56/0.99  bmc1_current_bound:                     -1
% 3.56/0.99  bmc1_last_solved_bound:                 -1
% 3.56/0.99  bmc1_unsat_core_size:                   -1
% 3.56/0.99  bmc1_unsat_core_parents_size:           -1
% 3.56/0.99  bmc1_merge_next_fun:                    0
% 3.56/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.56/0.99  
% 3.56/0.99  ------ Instantiation
% 3.56/0.99  
% 3.56/0.99  inst_num_of_clauses:                    1124
% 3.56/0.99  inst_num_in_passive:                    527
% 3.56/0.99  inst_num_in_active:                     492
% 3.56/0.99  inst_num_in_unprocessed:                107
% 3.56/0.99  inst_num_of_loops:                      510
% 3.56/0.99  inst_num_of_learning_restarts:          0
% 3.56/0.99  inst_num_moves_active_passive:          15
% 3.56/0.99  inst_lit_activity:                      0
% 3.56/0.99  inst_lit_activity_moves:                0
% 3.56/0.99  inst_num_tautologies:                   0
% 3.56/0.99  inst_num_prop_implied:                  0
% 3.56/0.99  inst_num_existing_simplified:           0
% 3.56/0.99  inst_num_eq_res_simplified:             0
% 3.56/0.99  inst_num_child_elim:                    0
% 3.56/0.99  inst_num_of_dismatching_blockings:      327
% 3.56/0.99  inst_num_of_non_proper_insts:           1130
% 3.56/0.99  inst_num_of_duplicates:                 0
% 3.56/0.99  inst_inst_num_from_inst_to_res:         0
% 3.56/0.99  inst_dismatching_checking_time:         0.
% 3.56/0.99  
% 3.56/0.99  ------ Resolution
% 3.56/0.99  
% 3.56/0.99  res_num_of_clauses:                     0
% 3.56/0.99  res_num_in_passive:                     0
% 3.56/0.99  res_num_in_active:                      0
% 3.56/0.99  res_num_of_loops:                       95
% 3.56/0.99  res_forward_subset_subsumed:            91
% 3.56/0.99  res_backward_subset_subsumed:           4
% 3.56/0.99  res_forward_subsumed:                   0
% 3.56/0.99  res_backward_subsumed:                  0
% 3.56/0.99  res_forward_subsumption_resolution:     0
% 3.56/0.99  res_backward_subsumption_resolution:    0
% 3.56/0.99  res_clause_to_clause_subsumption:       215
% 3.56/0.99  res_orphan_elimination:                 0
% 3.56/0.99  res_tautology_del:                      104
% 3.56/0.99  res_num_eq_res_simplified:              0
% 3.56/0.99  res_num_sel_changes:                    0
% 3.56/0.99  res_moves_from_active_to_pass:          0
% 3.56/0.99  
% 3.56/0.99  ------ Superposition
% 3.56/0.99  
% 3.56/0.99  sup_time_total:                         0.
% 3.56/0.99  sup_time_generating:                    0.
% 3.56/0.99  sup_time_sim_full:                      0.
% 3.56/0.99  sup_time_sim_immed:                     0.
% 3.56/0.99  
% 3.56/0.99  sup_num_of_clauses:                     68
% 3.56/0.99  sup_num_in_active:                      65
% 3.56/0.99  sup_num_in_passive:                     3
% 3.56/0.99  sup_num_of_loops:                       100
% 3.56/0.99  sup_fw_superposition:                   95
% 3.56/0.99  sup_bw_superposition:                   56
% 3.56/0.99  sup_immediate_simplified:               26
% 3.56/0.99  sup_given_eliminated:                   1
% 3.56/0.99  comparisons_done:                       0
% 3.56/0.99  comparisons_avoided:                    0
% 3.56/0.99  
% 3.56/0.99  ------ Simplifications
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  sim_fw_subset_subsumed:                 0
% 3.56/0.99  sim_bw_subset_subsumed:                 0
% 3.56/0.99  sim_fw_subsumed:                        3
% 3.56/0.99  sim_bw_subsumed:                        0
% 3.56/0.99  sim_fw_subsumption_res:                 0
% 3.56/0.99  sim_bw_subsumption_res:                 0
% 3.56/0.99  sim_tautology_del:                      0
% 3.56/0.99  sim_eq_tautology_del:                   7
% 3.56/0.99  sim_eq_res_simp:                        0
% 3.56/0.99  sim_fw_demodulated:                     11
% 3.56/0.99  sim_bw_demodulated:                     35
% 3.56/0.99  sim_light_normalised:                   27
% 3.56/0.99  sim_joinable_taut:                      0
% 3.56/0.99  sim_joinable_simp:                      0
% 3.56/0.99  sim_ac_normalised:                      0
% 3.56/0.99  sim_smt_subsumption:                    0
% 3.56/0.99  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:11 EST 2020

% Result     : CounterSatisfiable 8.04s
% Output     : Saturation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  392 (104543 expanded)
%              Number of clauses        :  315 (11888 expanded)
%              Number of leaves         :   27 (33632 expanded)
%              Depth                    :   25
%              Number of atoms          :  472 (119778 expanded)
%              Number of equality atoms :  405 (108242 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f66])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f74,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f45,f68,f68])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f42,f68])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f44,f68])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f42])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f42])).

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

fof(f26,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f32])).

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f36,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f35,f34])).

fof(f62,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f44])).

fof(f61,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_102,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_176,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_13,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_874,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_13])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3828,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_874,c_4])).

cnf(c_3838,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3828,c_13])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_875,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_7701,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_875])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7728,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_7701,c_5,c_7])).

cnf(c_12080,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3838,c_7728])).

cnf(c_7708,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_875,c_7])).

cnf(c_8127,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3838,c_7708])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3829,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_874,c_0])).

cnf(c_3837,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3829,c_13])).

cnf(c_3984,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_874,c_3837])).

cnf(c_569,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_577,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_569,c_3])).

cnf(c_1166,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_577,c_0])).

cnf(c_1171,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1166,c_5])).

cnf(c_516,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_519,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_516,c_3])).

cnf(c_1256,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1171,c_519])).

cnf(c_4023,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3984,c_13,c_1256,c_3838])).

cnf(c_4519,plain,
    ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_874,c_4023])).

cnf(c_4568,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4519,c_13])).

cnf(c_8165,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_8127,c_5,c_4568])).

cnf(c_12096,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_12080,c_8165])).

cnf(c_12097,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_12096,c_7,c_3838,c_8165])).

cnf(c_15641,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3838,c_12097])).

cnf(c_40383,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_874,c_15641])).

cnf(c_40495,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_40383,c_13])).

cnf(c_2,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4624,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_4568])).

cnf(c_9703,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4624,c_8165])).

cnf(c_4742,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2,c_3838])).

cnf(c_9706,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9703,c_4742])).

cnf(c_7715,plain,
    ( k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_875,c_3])).

cnf(c_7718,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7715,c_7])).

cnf(c_9707,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_9706,c_5,c_1171,c_7718])).

cnf(c_3820,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_874])).

cnf(c_12927,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0 ),
    inference(demodulation,[status(thm)],[c_3820,c_13,c_9707])).

cnf(c_12946,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9707,c_12927])).

cnf(c_4503,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_4023])).

cnf(c_7711,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_875,c_4503])).

cnf(c_7721,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7711,c_7])).

cnf(c_9567,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7721,c_7708])).

cnf(c_7714,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_875,c_2])).

cnf(c_7719,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_7714,c_7])).

cnf(c_3824,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_874,c_13])).

cnf(c_9434,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_7719,c_3824])).

cnf(c_9443,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9434,c_3,c_1171])).

cnf(c_9588,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_9567,c_5,c_9443])).

cnf(c_12989,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_12946,c_9588])).

cnf(c_39742,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7708,c_12989])).

cnf(c_7935,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7718,c_875])).

cnf(c_7976,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_7935,c_5,c_7])).

cnf(c_12240,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9707,c_7976])).

cnf(c_8132,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4503,c_7708])).

cnf(c_8154,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_8132,c_5])).

cnf(c_12284,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_12240,c_8154,c_9588])).

cnf(c_38352,plain,
    ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_875,c_12284])).

cnf(c_38585,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_38352,c_7])).

cnf(c_4675,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4568,c_874])).

cnf(c_4682,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_4675,c_13,c_1171])).

cnf(c_11876,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_874,c_4682])).

cnf(c_11953,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11876,c_13])).

cnf(c_12443,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11953,c_875])).

cnf(c_4552,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4023,c_874])).

cnf(c_4559,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4552,c_13,c_1171])).

cnf(c_8113,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_874,c_7708])).

cnf(c_8190,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8113,c_5,c_4023])).

cnf(c_8191,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_8190,c_13])).

cnf(c_12527,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_12443,c_7,c_4559,c_8191])).

cnf(c_12721,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7719,c_12527])).

cnf(c_36412,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7708,c_12721])).

cnf(c_12740,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9443,c_12527])).

cnf(c_34517,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7708,c_12740])).

cnf(c_12722,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9707,c_12527])).

cnf(c_34019,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7708,c_12722])).

cnf(c_12067,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9707,c_7728])).

cnf(c_12120,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_12067,c_8154,c_9588])).

cnf(c_31961,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(k4_xboole_0(X0,X1),X1))) ),
    inference(superposition,[status(thm)],[c_9707,c_12120])).

cnf(c_32023,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_31961,c_4503,c_9588])).

cnf(c_10507,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9707,c_9707])).

cnf(c_10530,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_10507,c_4503,c_9588])).

cnf(c_12076,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3824,c_7728])).

cnf(c_3833,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_874,c_3])).

cnf(c_3834,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3833,c_13])).

cnf(c_8126,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3834,c_7708])).

cnf(c_8166,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_8126,c_5])).

cnf(c_8192,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_8191,c_8166])).

cnf(c_12102,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12076,c_8191,c_8192])).

cnf(c_31316,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10530,c_12102])).

cnf(c_12959,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4023,c_12927])).

cnf(c_12975,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_12959,c_5])).

cnf(c_24114,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10530,c_12975])).

cnf(c_24328,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_24114,c_1171,c_12989])).

cnf(c_8105,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_7708])).

cnf(c_8206,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_8105,c_5,c_4023])).

cnf(c_24130,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10530,c_8206])).

cnf(c_7875,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_7718])).

cnf(c_24318,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_24130,c_7875])).

cnf(c_9851,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3838,c_8191])).

cnf(c_9880,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9851,c_4568])).

cnf(c_23321,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4568,c_9880])).

cnf(c_3827,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_874,c_0])).

cnf(c_572,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_3839,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3827,c_13,c_572])).

cnf(c_23703,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_23321,c_3839])).

cnf(c_4793,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_3838,c_3838])).

cnf(c_4807,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4793,c_4568])).

cnf(c_9426,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7719,c_572])).

cnf(c_9455,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_9426,c_7719,c_9443])).

cnf(c_19844,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3838,c_9455])).

cnf(c_19851,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_19844,c_8165])).

cnf(c_22326,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4807,c_19851])).

cnf(c_22414,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_22326,c_4807])).

cnf(c_22360,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4807,c_7708])).

cnf(c_22377,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_22360,c_4807])).

cnf(c_4674,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4568,c_3824])).

cnf(c_4683,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4674,c_3838,c_3839])).

cnf(c_20786,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4568,c_4683])).

cnf(c_21367,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_20786,c_3839])).

cnf(c_20883,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4683,c_12527])).

cnf(c_20164,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7875,c_19851])).

cnf(c_20556,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_20164,c_7875])).

cnf(c_11902,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3838,c_4682])).

cnf(c_11916,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_11902,c_13,c_3839])).

cnf(c_17700,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_11916])).

cnf(c_12713,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_12527])).

cnf(c_16887,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_12713])).

cnf(c_17474,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9707,c_16887])).

cnf(c_17519,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_17474,c_4503,c_8154,c_9588])).

cnf(c_17115,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9707,c_12713])).

cnf(c_17231,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_17115,c_4503,c_8154,c_9588])).

cnf(c_17099,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7708,c_12713])).

cnf(c_12084,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9443,c_7728])).

cnf(c_12087,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_12084,c_9588])).

cnf(c_12088,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_12087,c_7,c_9443,c_9588])).

cnf(c_14860,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_875,c_12088])).

cnf(c_14937,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_14860,c_7])).

cnf(c_15270,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_9707,c_14937])).

cnf(c_15322,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_15270,c_4503,c_9588])).

cnf(c_11898,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3824,c_4682])).

cnf(c_11923,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_11898,c_4,c_3838])).

cnf(c_13800,plain,
    ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_874,c_11923])).

cnf(c_13817,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_13800,c_13])).

cnf(c_13413,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2,c_12975])).

cnf(c_13464,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_13413,c_2])).

cnf(c_13421,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_7719,c_12975])).

cnf(c_13458,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13421,c_13,c_7719])).

cnf(c_13433,plain,
    ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_874,c_12975])).

cnf(c_13448,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_13433,c_13])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_119,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_120,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_119])).

cnf(c_515,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_120,c_0])).

cnf(c_520,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_515,c_5])).

cnf(c_3972,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_520,c_3837])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_297,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k4_xboole_0(X2,X0)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_300,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_458,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k4_xboole_0(X0,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_297,c_300])).

cnf(c_629,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_298,c_458])).

cnf(c_16,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_633,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_629,c_16])).

cnf(c_635,plain,
    ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_633,c_3])).

cnf(c_682,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(sK1,k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_635,c_4])).

cnf(c_690,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_682,c_635])).

cnf(c_567,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_120,c_4])).

cnf(c_579,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_567,c_520])).

cnf(c_691,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_690,c_579])).

cnf(c_4032,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3972,c_691])).

cnf(c_4033,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_4032,c_5])).

cnf(c_12949,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_4033,c_12927])).

cnf(c_4049,plain,
    ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4033,c_633])).

cnf(c_12986,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_12949,c_4049])).

cnf(c_7884,plain,
    ( k4_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4033,c_7718])).

cnf(c_8005,plain,
    ( k4_xboole_0(sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7884,c_4049])).

cnf(c_634,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_633,c_2])).

cnf(c_636,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_634,c_520])).

cnf(c_3875,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0))) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_636,c_3824])).

cnf(c_8376,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8005,c_3875])).

cnf(c_8381,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_8376,c_1171])).

cnf(c_12728,plain,
    ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_8381,c_12527])).

cnf(c_12726,plain,
    ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_636,c_12527])).

cnf(c_12732,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_3824,c_12527])).

cnf(c_12424,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4568,c_11953])).

cnf(c_12548,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_12424,c_3839])).

cnf(c_12224,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7708,c_7976])).

cnf(c_12071,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k4_xboole_0(k2_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_636,c_7728])).

cnf(c_695,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,sK1),sK1) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_520,c_2])).

cnf(c_1650,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))) = k4_xboole_0(k5_xboole_0(sK2,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_695,c_4])).

cnf(c_1657,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_1650,c_695])).

cnf(c_3876,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_695,c_3824])).

cnf(c_4489,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1657,c_1657,c_3876,c_4033])).

cnf(c_8131,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK2) ),
    inference(superposition,[status(thm)],[c_4489,c_7708])).

cnf(c_7878,plain,
    ( k4_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_520,c_7718])).

cnf(c_8155,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),sK2) ),
    inference(light_normalisation,[status(thm)],[c_8131,c_7878])).

cnf(c_8156,plain,
    ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8155,c_5,c_1171,c_4049,c_7878])).

cnf(c_12113,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_12071,c_636,c_8156])).

cnf(c_12073,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_8381,c_7728])).

cnf(c_8109,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k2_struct_0(sK0),sK1)) = k5_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_635,c_7708])).

cnf(c_8200,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8109,c_5])).

cnf(c_12109,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_12073,c_4049,c_8200])).

cnf(c_12079,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_4023,c_7728])).

cnf(c_12098,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12079,c_5,c_4023])).

cnf(c_12051,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7708,c_7728])).

cnf(c_2322,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_572])).

cnf(c_2386,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2322,c_2])).

cnf(c_11686,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_2386,c_2386,c_9707])).

cnf(c_11703,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9707,c_11686])).

cnf(c_11809,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_11703,c_4503,c_9588])).

cnf(c_11444,plain,
    ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_636,c_4559])).

cnf(c_11473,plain,
    ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_11444,c_636])).

cnf(c_11579,plain,
    ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_6,c_11473])).

cnf(c_11431,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2,c_4559])).

cnf(c_11486,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_11431,c_2])).

cnf(c_11436,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1171,c_4559])).

cnf(c_11481,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11436,c_1171])).

cnf(c_11438,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7718,c_4559])).

cnf(c_11479,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11438,c_7718])).

cnf(c_11439,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_7719,c_4559])).

cnf(c_11478,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_11439,c_7719])).

cnf(c_11440,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9707,c_4559])).

cnf(c_11477,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_11440,c_9707])).

cnf(c_11446,plain,
    ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_8381,c_4559])).

cnf(c_11471,plain,
    ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_11446,c_8381])).

cnf(c_11457,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9443,c_4559])).

cnf(c_11461,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11457,c_9443])).

cnf(c_11449,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3824,c_4559])).

cnf(c_743,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_636,c_4])).

cnf(c_748,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_743,c_636])).

cnf(c_2056,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_748,c_0])).

cnf(c_11110,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_8381,c_2056])).

cnf(c_10920,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7875,c_7708])).

cnf(c_10938,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_10920,c_7875])).

cnf(c_10923,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7875,c_3837])).

cnf(c_10932,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10923,c_7875])).

cnf(c_10933,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10932,c_1171])).

cnf(c_10924,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7875,c_3824])).

cnf(c_10931,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_10924,c_7875])).

cnf(c_1268,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1171,c_3])).

cnf(c_1763,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1268])).

cnf(c_1817,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1763,c_4])).

cnf(c_7705,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1817,c_875])).

cnf(c_7726,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7705,c_5])).

cnf(c_10727,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_7726])).

cnf(c_9701,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4568,c_8165])).

cnf(c_9710,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9701,c_3839])).

cnf(c_9428,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_7719,c_0])).

cnf(c_9453,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_9428,c_7719,c_9443])).

cnf(c_9435,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7719,c_874])).

cnf(c_9444,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_9443,c_9435])).

cnf(c_457,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k5_xboole_0(sK2,k4_xboole_0(X0,sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_298,c_300])).

cnf(c_587,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_297,c_457])).

cnf(c_589,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_587,c_520])).

cnf(c_8444,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8156,c_589])).

cnf(c_8405,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_8005,c_3837])).

cnf(c_8412,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK2,k1_xboole_0)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_8405,c_636])).

cnf(c_8413,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_8412,c_1171])).

cnf(c_8114,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1817,c_7708])).

cnf(c_8189,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8114,c_5,c_1171])).

cnf(c_10,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_301,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_303,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_301,c_8])).

cnf(c_459,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_303,c_300])).

cnf(c_804,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_297,c_459])).

cnf(c_8044,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(demodulation,[status(thm)],[c_7708,c_804])).

cnf(c_803,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_298,c_459])).

cnf(c_8043,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(demodulation,[status(thm)],[c_7708,c_803])).

cnf(c_7949,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_7718,c_3837])).

cnf(c_7956,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7949,c_2])).

cnf(c_7957,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7956,c_1171])).

cnf(c_4794,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_3838,c_3837])).

cnf(c_4806,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4794,c_4568])).

cnf(c_4055,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_4033,c_3824])).

cnf(c_4063,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4055,c_520,c_691])).

cnf(c_586,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_298,c_457])).

cnf(c_590,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_586,c_572])).

cnf(c_4203,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4063,c_590])).

cnf(c_4204,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_4203,c_1171])).

cnf(c_3821,plain,
    ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1171,c_874])).

cnf(c_1173,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1171,c_577])).

cnf(c_3845,plain,
    ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3821,c_1173])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_299,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3315,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_303,c_299])).

cnf(c_3314,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_297,c_299])).

cnf(c_3313,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_298,c_299])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_302,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3190,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_303,c_302])).

cnf(c_3191,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3190,c_1173])).

cnf(c_3189,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_297,c_302])).

cnf(c_3188,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_298,c_302])).

cnf(c_805,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_303,c_459])).

cnf(c_2234,plain,
    ( k4_subset_1(X0,X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_805,c_5,c_805,c_1173])).

cnf(c_630,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_297,c_458])).

cnf(c_632,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_630,c_572])).

cnf(c_1026,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_632,c_579,c_632,c_691])).

cnf(c_631,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_303,c_458])).

cnf(c_588,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_303,c_457])).

cnf(c_14,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f63])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:53:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.04/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.04/1.48  
% 8.04/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.04/1.48  
% 8.04/1.48  ------  iProver source info
% 8.04/1.48  
% 8.04/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.04/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.04/1.48  git: non_committed_changes: false
% 8.04/1.48  git: last_make_outside_of_git: false
% 8.04/1.48  
% 8.04/1.48  ------ 
% 8.04/1.48  
% 8.04/1.48  ------ Input Options
% 8.04/1.48  
% 8.04/1.48  --out_options                           all
% 8.04/1.48  --tptp_safe_out                         true
% 8.04/1.48  --problem_path                          ""
% 8.04/1.48  --include_path                          ""
% 8.04/1.48  --clausifier                            res/vclausify_rel
% 8.04/1.48  --clausifier_options                    ""
% 8.04/1.48  --stdin                                 false
% 8.04/1.48  --stats_out                             all
% 8.04/1.48  
% 8.04/1.48  ------ General Options
% 8.04/1.48  
% 8.04/1.48  --fof                                   false
% 8.04/1.48  --time_out_real                         305.
% 8.04/1.48  --time_out_virtual                      -1.
% 8.04/1.48  --symbol_type_check                     false
% 8.04/1.48  --clausify_out                          false
% 8.04/1.48  --sig_cnt_out                           false
% 8.04/1.48  --trig_cnt_out                          false
% 8.04/1.48  --trig_cnt_out_tolerance                1.
% 8.04/1.48  --trig_cnt_out_sk_spl                   false
% 8.04/1.48  --abstr_cl_out                          false
% 8.04/1.48  
% 8.04/1.48  ------ Global Options
% 8.04/1.48  
% 8.04/1.48  --schedule                              default
% 8.04/1.48  --add_important_lit                     false
% 8.04/1.48  --prop_solver_per_cl                    1000
% 8.04/1.48  --min_unsat_core                        false
% 8.04/1.48  --soft_assumptions                      false
% 8.04/1.48  --soft_lemma_size                       3
% 8.04/1.48  --prop_impl_unit_size                   0
% 8.04/1.48  --prop_impl_unit                        []
% 8.04/1.48  --share_sel_clauses                     true
% 8.04/1.48  --reset_solvers                         false
% 8.04/1.48  --bc_imp_inh                            [conj_cone]
% 8.04/1.48  --conj_cone_tolerance                   3.
% 8.04/1.48  --extra_neg_conj                        none
% 8.04/1.48  --large_theory_mode                     true
% 8.04/1.48  --prolific_symb_bound                   200
% 8.04/1.48  --lt_threshold                          2000
% 8.04/1.48  --clause_weak_htbl                      true
% 8.04/1.48  --gc_record_bc_elim                     false
% 8.04/1.48  
% 8.04/1.48  ------ Preprocessing Options
% 8.04/1.48  
% 8.04/1.48  --preprocessing_flag                    true
% 8.04/1.48  --time_out_prep_mult                    0.1
% 8.04/1.48  --splitting_mode                        input
% 8.04/1.48  --splitting_grd                         true
% 8.04/1.48  --splitting_cvd                         false
% 8.04/1.48  --splitting_cvd_svl                     false
% 8.04/1.48  --splitting_nvd                         32
% 8.04/1.48  --sub_typing                            true
% 8.04/1.48  --prep_gs_sim                           true
% 8.04/1.48  --prep_unflatten                        true
% 8.04/1.48  --prep_res_sim                          true
% 8.04/1.48  --prep_upred                            true
% 8.04/1.48  --prep_sem_filter                       exhaustive
% 8.04/1.48  --prep_sem_filter_out                   false
% 8.04/1.48  --pred_elim                             true
% 8.04/1.48  --res_sim_input                         true
% 8.04/1.48  --eq_ax_congr_red                       true
% 8.04/1.48  --pure_diseq_elim                       true
% 8.04/1.48  --brand_transform                       false
% 8.04/1.48  --non_eq_to_eq                          false
% 8.04/1.48  --prep_def_merge                        true
% 8.04/1.48  --prep_def_merge_prop_impl              false
% 8.04/1.48  --prep_def_merge_mbd                    true
% 8.04/1.48  --prep_def_merge_tr_red                 false
% 8.04/1.48  --prep_def_merge_tr_cl                  false
% 8.04/1.48  --smt_preprocessing                     true
% 8.04/1.48  --smt_ac_axioms                         fast
% 8.04/1.48  --preprocessed_out                      false
% 8.04/1.48  --preprocessed_stats                    false
% 8.04/1.48  
% 8.04/1.48  ------ Abstraction refinement Options
% 8.04/1.48  
% 8.04/1.48  --abstr_ref                             []
% 8.04/1.48  --abstr_ref_prep                        false
% 8.04/1.48  --abstr_ref_until_sat                   false
% 8.04/1.48  --abstr_ref_sig_restrict                funpre
% 8.04/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.48  --abstr_ref_under                       []
% 8.04/1.48  
% 8.04/1.48  ------ SAT Options
% 8.04/1.48  
% 8.04/1.48  --sat_mode                              false
% 8.04/1.48  --sat_fm_restart_options                ""
% 8.04/1.48  --sat_gr_def                            false
% 8.04/1.48  --sat_epr_types                         true
% 8.04/1.48  --sat_non_cyclic_types                  false
% 8.04/1.48  --sat_finite_models                     false
% 8.04/1.48  --sat_fm_lemmas                         false
% 8.04/1.48  --sat_fm_prep                           false
% 8.04/1.48  --sat_fm_uc_incr                        true
% 8.04/1.48  --sat_out_model                         small
% 8.04/1.48  --sat_out_clauses                       false
% 8.04/1.48  
% 8.04/1.48  ------ QBF Options
% 8.04/1.48  
% 8.04/1.48  --qbf_mode                              false
% 8.04/1.48  --qbf_elim_univ                         false
% 8.04/1.48  --qbf_dom_inst                          none
% 8.04/1.48  --qbf_dom_pre_inst                      false
% 8.04/1.48  --qbf_sk_in                             false
% 8.04/1.48  --qbf_pred_elim                         true
% 8.04/1.48  --qbf_split                             512
% 8.04/1.48  
% 8.04/1.48  ------ BMC1 Options
% 8.04/1.48  
% 8.04/1.48  --bmc1_incremental                      false
% 8.04/1.48  --bmc1_axioms                           reachable_all
% 8.04/1.48  --bmc1_min_bound                        0
% 8.04/1.48  --bmc1_max_bound                        -1
% 8.04/1.48  --bmc1_max_bound_default                -1
% 8.04/1.48  --bmc1_symbol_reachability              true
% 8.04/1.48  --bmc1_property_lemmas                  false
% 8.04/1.48  --bmc1_k_induction                      false
% 8.04/1.48  --bmc1_non_equiv_states                 false
% 8.04/1.48  --bmc1_deadlock                         false
% 8.04/1.48  --bmc1_ucm                              false
% 8.04/1.48  --bmc1_add_unsat_core                   none
% 8.04/1.48  --bmc1_unsat_core_children              false
% 8.04/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.48  --bmc1_out_stat                         full
% 8.04/1.48  --bmc1_ground_init                      false
% 8.04/1.48  --bmc1_pre_inst_next_state              false
% 8.04/1.48  --bmc1_pre_inst_state                   false
% 8.04/1.48  --bmc1_pre_inst_reach_state             false
% 8.04/1.48  --bmc1_out_unsat_core                   false
% 8.04/1.48  --bmc1_aig_witness_out                  false
% 8.04/1.48  --bmc1_verbose                          false
% 8.04/1.48  --bmc1_dump_clauses_tptp                false
% 8.04/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.48  --bmc1_dump_file                        -
% 8.04/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.48  --bmc1_ucm_extend_mode                  1
% 8.04/1.48  --bmc1_ucm_init_mode                    2
% 8.04/1.48  --bmc1_ucm_cone_mode                    none
% 8.04/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.48  --bmc1_ucm_relax_model                  4
% 8.04/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.48  --bmc1_ucm_layered_model                none
% 8.04/1.48  --bmc1_ucm_max_lemma_size               10
% 8.04/1.48  
% 8.04/1.48  ------ AIG Options
% 8.04/1.48  
% 8.04/1.48  --aig_mode                              false
% 8.04/1.48  
% 8.04/1.48  ------ Instantiation Options
% 8.04/1.48  
% 8.04/1.48  --instantiation_flag                    true
% 8.04/1.48  --inst_sos_flag                         true
% 8.04/1.48  --inst_sos_phase                        true
% 8.04/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.48  --inst_lit_sel_side                     num_symb
% 8.04/1.48  --inst_solver_per_active                1400
% 8.04/1.48  --inst_solver_calls_frac                1.
% 8.04/1.48  --inst_passive_queue_type               priority_queues
% 8.04/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.48  --inst_passive_queues_freq              [25;2]
% 8.04/1.48  --inst_dismatching                      true
% 8.04/1.48  --inst_eager_unprocessed_to_passive     true
% 8.04/1.48  --inst_prop_sim_given                   true
% 8.04/1.48  --inst_prop_sim_new                     false
% 8.04/1.48  --inst_subs_new                         false
% 8.04/1.48  --inst_eq_res_simp                      false
% 8.04/1.48  --inst_subs_given                       false
% 8.04/1.48  --inst_orphan_elimination               true
% 8.04/1.48  --inst_learning_loop_flag               true
% 8.04/1.48  --inst_learning_start                   3000
% 8.04/1.48  --inst_learning_factor                  2
% 8.04/1.48  --inst_start_prop_sim_after_learn       3
% 8.04/1.48  --inst_sel_renew                        solver
% 8.04/1.48  --inst_lit_activity_flag                true
% 8.04/1.48  --inst_restr_to_given                   false
% 8.04/1.48  --inst_activity_threshold               500
% 8.04/1.48  --inst_out_proof                        true
% 8.04/1.48  
% 8.04/1.48  ------ Resolution Options
% 8.04/1.48  
% 8.04/1.48  --resolution_flag                       true
% 8.04/1.48  --res_lit_sel                           adaptive
% 8.04/1.48  --res_lit_sel_side                      none
% 8.04/1.48  --res_ordering                          kbo
% 8.04/1.48  --res_to_prop_solver                    active
% 8.04/1.48  --res_prop_simpl_new                    false
% 8.04/1.48  --res_prop_simpl_given                  true
% 8.04/1.48  --res_passive_queue_type                priority_queues
% 8.04/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.48  --res_passive_queues_freq               [15;5]
% 8.04/1.48  --res_forward_subs                      full
% 8.04/1.48  --res_backward_subs                     full
% 8.04/1.48  --res_forward_subs_resolution           true
% 8.04/1.48  --res_backward_subs_resolution          true
% 8.04/1.48  --res_orphan_elimination                true
% 8.04/1.48  --res_time_limit                        2.
% 8.04/1.48  --res_out_proof                         true
% 8.04/1.48  
% 8.04/1.48  ------ Superposition Options
% 8.04/1.48  
% 8.04/1.48  --superposition_flag                    true
% 8.04/1.48  --sup_passive_queue_type                priority_queues
% 8.04/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.48  --demod_completeness_check              fast
% 8.04/1.48  --demod_use_ground                      true
% 8.04/1.48  --sup_to_prop_solver                    passive
% 8.04/1.48  --sup_prop_simpl_new                    true
% 8.04/1.48  --sup_prop_simpl_given                  true
% 8.04/1.48  --sup_fun_splitting                     true
% 8.04/1.48  --sup_smt_interval                      50000
% 8.04/1.48  
% 8.04/1.48  ------ Superposition Simplification Setup
% 8.04/1.48  
% 8.04/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.04/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.04/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.04/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.04/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.04/1.48  --sup_immed_triv                        [TrivRules]
% 8.04/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.48  --sup_immed_bw_main                     []
% 8.04/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.04/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.48  --sup_input_bw                          []
% 8.04/1.48  
% 8.04/1.48  ------ Combination Options
% 8.04/1.48  
% 8.04/1.48  --comb_res_mult                         3
% 8.04/1.48  --comb_sup_mult                         2
% 8.04/1.48  --comb_inst_mult                        10
% 8.04/1.48  
% 8.04/1.48  ------ Debug Options
% 8.04/1.48  
% 8.04/1.48  --dbg_backtrace                         false
% 8.04/1.48  --dbg_dump_prop_clauses                 false
% 8.04/1.48  --dbg_dump_prop_clauses_file            -
% 8.04/1.48  --dbg_out_stat                          false
% 8.04/1.48  ------ Parsing...
% 8.04/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.04/1.48  
% 8.04/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 8.04/1.48  
% 8.04/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.04/1.48  
% 8.04/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.04/1.48  ------ Proving...
% 8.04/1.48  ------ Problem Properties 
% 8.04/1.48  
% 8.04/1.48  
% 8.04/1.48  clauses                                 18
% 8.04/1.48  conjectures                             4
% 8.04/1.48  EPR                                     0
% 8.04/1.48  Horn                                    18
% 8.04/1.48  unary                                   15
% 8.04/1.48  binary                                  2
% 8.04/1.48  lits                                    22
% 8.04/1.48  lits eq                                 15
% 8.04/1.48  fd_pure                                 0
% 8.04/1.48  fd_pseudo                               0
% 8.04/1.48  fd_cond                                 0
% 8.04/1.48  fd_pseudo_cond                          0
% 8.04/1.48  AC symbols                              0
% 8.04/1.48  
% 8.04/1.48  ------ Schedule dynamic 5 is on 
% 8.04/1.48  
% 8.04/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.04/1.48  
% 8.04/1.48  
% 8.04/1.48  ------ 
% 8.04/1.48  Current options:
% 8.04/1.48  ------ 
% 8.04/1.48  
% 8.04/1.48  ------ Input Options
% 8.04/1.48  
% 8.04/1.48  --out_options                           all
% 8.04/1.48  --tptp_safe_out                         true
% 8.04/1.48  --problem_path                          ""
% 8.04/1.48  --include_path                          ""
% 8.04/1.48  --clausifier                            res/vclausify_rel
% 8.04/1.48  --clausifier_options                    ""
% 8.04/1.48  --stdin                                 false
% 8.04/1.48  --stats_out                             all
% 8.04/1.48  
% 8.04/1.48  ------ General Options
% 8.04/1.48  
% 8.04/1.48  --fof                                   false
% 8.04/1.48  --time_out_real                         305.
% 8.04/1.48  --time_out_virtual                      -1.
% 8.04/1.48  --symbol_type_check                     false
% 8.04/1.48  --clausify_out                          false
% 8.04/1.48  --sig_cnt_out                           false
% 8.04/1.48  --trig_cnt_out                          false
% 8.04/1.48  --trig_cnt_out_tolerance                1.
% 8.04/1.48  --trig_cnt_out_sk_spl                   false
% 8.04/1.48  --abstr_cl_out                          false
% 8.04/1.48  
% 8.04/1.48  ------ Global Options
% 8.04/1.48  
% 8.04/1.48  --schedule                              default
% 8.04/1.48  --add_important_lit                     false
% 8.04/1.48  --prop_solver_per_cl                    1000
% 8.04/1.48  --min_unsat_core                        false
% 8.04/1.48  --soft_assumptions                      false
% 8.04/1.48  --soft_lemma_size                       3
% 8.04/1.48  --prop_impl_unit_size                   0
% 8.04/1.48  --prop_impl_unit                        []
% 8.04/1.48  --share_sel_clauses                     true
% 8.04/1.48  --reset_solvers                         false
% 8.04/1.48  --bc_imp_inh                            [conj_cone]
% 8.04/1.48  --conj_cone_tolerance                   3.
% 8.04/1.48  --extra_neg_conj                        none
% 8.04/1.48  --large_theory_mode                     true
% 8.04/1.48  --prolific_symb_bound                   200
% 8.04/1.48  --lt_threshold                          2000
% 8.04/1.48  --clause_weak_htbl                      true
% 8.04/1.48  --gc_record_bc_elim                     false
% 8.04/1.48  
% 8.04/1.48  ------ Preprocessing Options
% 8.04/1.48  
% 8.04/1.48  --preprocessing_flag                    true
% 8.04/1.48  --time_out_prep_mult                    0.1
% 8.04/1.48  --splitting_mode                        input
% 8.04/1.48  --splitting_grd                         true
% 8.04/1.48  --splitting_cvd                         false
% 8.04/1.48  --splitting_cvd_svl                     false
% 8.04/1.48  --splitting_nvd                         32
% 8.04/1.48  --sub_typing                            true
% 8.04/1.48  --prep_gs_sim                           true
% 8.04/1.48  --prep_unflatten                        true
% 8.04/1.48  --prep_res_sim                          true
% 8.04/1.48  --prep_upred                            true
% 8.04/1.48  --prep_sem_filter                       exhaustive
% 8.04/1.48  --prep_sem_filter_out                   false
% 8.04/1.48  --pred_elim                             true
% 8.04/1.48  --res_sim_input                         true
% 8.04/1.48  --eq_ax_congr_red                       true
% 8.04/1.48  --pure_diseq_elim                       true
% 8.04/1.48  --brand_transform                       false
% 8.04/1.48  --non_eq_to_eq                          false
% 8.04/1.48  --prep_def_merge                        true
% 8.04/1.48  --prep_def_merge_prop_impl              false
% 8.04/1.48  --prep_def_merge_mbd                    true
% 8.04/1.48  --prep_def_merge_tr_red                 false
% 8.04/1.48  --prep_def_merge_tr_cl                  false
% 8.04/1.48  --smt_preprocessing                     true
% 8.04/1.48  --smt_ac_axioms                         fast
% 8.04/1.48  --preprocessed_out                      false
% 8.04/1.48  --preprocessed_stats                    false
% 8.04/1.48  
% 8.04/1.48  ------ Abstraction refinement Options
% 8.04/1.48  
% 8.04/1.48  --abstr_ref                             []
% 8.04/1.48  --abstr_ref_prep                        false
% 8.04/1.48  --abstr_ref_until_sat                   false
% 8.04/1.48  --abstr_ref_sig_restrict                funpre
% 8.04/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.48  --abstr_ref_under                       []
% 8.04/1.48  
% 8.04/1.48  ------ SAT Options
% 8.04/1.48  
% 8.04/1.48  --sat_mode                              false
% 8.04/1.48  --sat_fm_restart_options                ""
% 8.04/1.48  --sat_gr_def                            false
% 8.04/1.48  --sat_epr_types                         true
% 8.04/1.48  --sat_non_cyclic_types                  false
% 8.04/1.48  --sat_finite_models                     false
% 8.04/1.48  --sat_fm_lemmas                         false
% 8.04/1.48  --sat_fm_prep                           false
% 8.04/1.48  --sat_fm_uc_incr                        true
% 8.04/1.48  --sat_out_model                         small
% 8.04/1.48  --sat_out_clauses                       false
% 8.04/1.48  
% 8.04/1.48  ------ QBF Options
% 8.04/1.48  
% 8.04/1.48  --qbf_mode                              false
% 8.04/1.48  --qbf_elim_univ                         false
% 8.04/1.48  --qbf_dom_inst                          none
% 8.04/1.48  --qbf_dom_pre_inst                      false
% 8.04/1.48  --qbf_sk_in                             false
% 8.04/1.48  --qbf_pred_elim                         true
% 8.04/1.48  --qbf_split                             512
% 8.04/1.48  
% 8.04/1.48  ------ BMC1 Options
% 8.04/1.48  
% 8.04/1.48  --bmc1_incremental                      false
% 8.04/1.48  --bmc1_axioms                           reachable_all
% 8.04/1.48  --bmc1_min_bound                        0
% 8.04/1.48  --bmc1_max_bound                        -1
% 8.04/1.48  --bmc1_max_bound_default                -1
% 8.04/1.48  --bmc1_symbol_reachability              true
% 8.04/1.48  --bmc1_property_lemmas                  false
% 8.04/1.48  --bmc1_k_induction                      false
% 8.04/1.48  --bmc1_non_equiv_states                 false
% 8.04/1.48  --bmc1_deadlock                         false
% 8.04/1.48  --bmc1_ucm                              false
% 8.04/1.48  --bmc1_add_unsat_core                   none
% 8.04/1.48  --bmc1_unsat_core_children              false
% 8.04/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.48  --bmc1_out_stat                         full
% 8.04/1.48  --bmc1_ground_init                      false
% 8.04/1.48  --bmc1_pre_inst_next_state              false
% 8.04/1.48  --bmc1_pre_inst_state                   false
% 8.04/1.48  --bmc1_pre_inst_reach_state             false
% 8.04/1.48  --bmc1_out_unsat_core                   false
% 8.04/1.48  --bmc1_aig_witness_out                  false
% 8.04/1.48  --bmc1_verbose                          false
% 8.04/1.48  --bmc1_dump_clauses_tptp                false
% 8.04/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.48  --bmc1_dump_file                        -
% 8.04/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.48  --bmc1_ucm_extend_mode                  1
% 8.04/1.48  --bmc1_ucm_init_mode                    2
% 8.04/1.48  --bmc1_ucm_cone_mode                    none
% 8.04/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.48  --bmc1_ucm_relax_model                  4
% 8.04/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.48  --bmc1_ucm_layered_model                none
% 8.04/1.48  --bmc1_ucm_max_lemma_size               10
% 8.04/1.48  
% 8.04/1.48  ------ AIG Options
% 8.04/1.48  
% 8.04/1.48  --aig_mode                              false
% 8.04/1.48  
% 8.04/1.48  ------ Instantiation Options
% 8.04/1.48  
% 8.04/1.48  --instantiation_flag                    true
% 8.04/1.48  --inst_sos_flag                         true
% 8.04/1.48  --inst_sos_phase                        true
% 8.04/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.48  --inst_lit_sel_side                     none
% 8.04/1.48  --inst_solver_per_active                1400
% 8.04/1.48  --inst_solver_calls_frac                1.
% 8.04/1.48  --inst_passive_queue_type               priority_queues
% 8.04/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.48  --inst_passive_queues_freq              [25;2]
% 8.04/1.48  --inst_dismatching                      true
% 8.04/1.48  --inst_eager_unprocessed_to_passive     true
% 8.04/1.48  --inst_prop_sim_given                   true
% 8.04/1.48  --inst_prop_sim_new                     false
% 8.04/1.48  --inst_subs_new                         false
% 8.04/1.48  --inst_eq_res_simp                      false
% 8.04/1.48  --inst_subs_given                       false
% 8.04/1.48  --inst_orphan_elimination               true
% 8.04/1.48  --inst_learning_loop_flag               true
% 8.04/1.48  --inst_learning_start                   3000
% 8.04/1.48  --inst_learning_factor                  2
% 8.04/1.48  --inst_start_prop_sim_after_learn       3
% 8.04/1.48  --inst_sel_renew                        solver
% 8.04/1.48  --inst_lit_activity_flag                true
% 8.04/1.48  --inst_restr_to_given                   false
% 8.04/1.48  --inst_activity_threshold               500
% 8.04/1.48  --inst_out_proof                        true
% 8.04/1.48  
% 8.04/1.48  ------ Resolution Options
% 8.04/1.48  
% 8.04/1.48  --resolution_flag                       false
% 8.04/1.48  --res_lit_sel                           adaptive
% 8.04/1.48  --res_lit_sel_side                      none
% 8.04/1.48  --res_ordering                          kbo
% 8.04/1.48  --res_to_prop_solver                    active
% 8.04/1.48  --res_prop_simpl_new                    false
% 8.04/1.48  --res_prop_simpl_given                  true
% 8.04/1.48  --res_passive_queue_type                priority_queues
% 8.04/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.48  --res_passive_queues_freq               [15;5]
% 8.04/1.48  --res_forward_subs                      full
% 8.04/1.48  --res_backward_subs                     full
% 8.04/1.48  --res_forward_subs_resolution           true
% 8.04/1.48  --res_backward_subs_resolution          true
% 8.04/1.48  --res_orphan_elimination                true
% 8.04/1.48  --res_time_limit                        2.
% 8.04/1.48  --res_out_proof                         true
% 8.04/1.48  
% 8.04/1.48  ------ Superposition Options
% 8.04/1.48  
% 8.04/1.48  --superposition_flag                    true
% 8.04/1.48  --sup_passive_queue_type                priority_queues
% 8.04/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.48  --demod_completeness_check              fast
% 8.04/1.48  --demod_use_ground                      true
% 8.04/1.48  --sup_to_prop_solver                    passive
% 8.04/1.48  --sup_prop_simpl_new                    true
% 8.04/1.48  --sup_prop_simpl_given                  true
% 8.04/1.48  --sup_fun_splitting                     true
% 8.04/1.48  --sup_smt_interval                      50000
% 8.04/1.48  
% 8.04/1.48  ------ Superposition Simplification Setup
% 8.04/1.48  
% 8.04/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.04/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.04/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.04/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.04/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.04/1.48  --sup_immed_triv                        [TrivRules]
% 8.04/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.48  --sup_immed_bw_main                     []
% 8.04/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.04/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.48  --sup_input_bw                          []
% 8.04/1.48  
% 8.04/1.48  ------ Combination Options
% 8.04/1.48  
% 8.04/1.48  --comb_res_mult                         3
% 8.04/1.48  --comb_sup_mult                         2
% 8.04/1.48  --comb_inst_mult                        10
% 8.04/1.48  
% 8.04/1.48  ------ Debug Options
% 8.04/1.48  
% 8.04/1.48  --dbg_backtrace                         false
% 8.04/1.48  --dbg_dump_prop_clauses                 false
% 8.04/1.48  --dbg_dump_prop_clauses_file            -
% 8.04/1.48  --dbg_out_stat                          false
% 8.04/1.48  
% 8.04/1.48  
% 8.04/1.48  
% 8.04/1.48  
% 8.04/1.48  ------ Proving...
% 8.04/1.48  
% 8.04/1.48  
% 8.04/1.48  % SZS status CounterSatisfiable for theBenchmark.p
% 8.04/1.48  
% 8.04/1.48  % SZS output start Saturation for theBenchmark.p
% 8.04/1.48  
% 8.04/1.48  fof(f9,axiom,(
% 8.04/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f45,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f9])).
% 8.04/1.48  
% 8.04/1.48  fof(f10,axiom,(
% 8.04/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f46,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f10])).
% 8.04/1.48  
% 8.04/1.48  fof(f11,axiom,(
% 8.04/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f47,plain,(
% 8.04/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f11])).
% 8.04/1.48  
% 8.04/1.48  fof(f12,axiom,(
% 8.04/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f48,plain,(
% 8.04/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f12])).
% 8.04/1.48  
% 8.04/1.48  fof(f13,axiom,(
% 8.04/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f49,plain,(
% 8.04/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f13])).
% 8.04/1.48  
% 8.04/1.48  fof(f14,axiom,(
% 8.04/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f50,plain,(
% 8.04/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f14])).
% 8.04/1.48  
% 8.04/1.48  fof(f15,axiom,(
% 8.04/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f51,plain,(
% 8.04/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f15])).
% 8.04/1.48  
% 8.04/1.48  fof(f64,plain,(
% 8.04/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 8.04/1.48    inference(definition_unfolding,[],[f50,f51])).
% 8.04/1.48  
% 8.04/1.48  fof(f65,plain,(
% 8.04/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 8.04/1.48    inference(definition_unfolding,[],[f49,f64])).
% 8.04/1.48  
% 8.04/1.48  fof(f66,plain,(
% 8.04/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 8.04/1.48    inference(definition_unfolding,[],[f48,f65])).
% 8.04/1.48  
% 8.04/1.48  fof(f67,plain,(
% 8.04/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 8.04/1.48    inference(definition_unfolding,[],[f47,f66])).
% 8.04/1.48  
% 8.04/1.48  fof(f68,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 8.04/1.48    inference(definition_unfolding,[],[f46,f67])).
% 8.04/1.48  
% 8.04/1.48  fof(f74,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 8.04/1.48    inference(definition_unfolding,[],[f45,f68,f68])).
% 8.04/1.48  
% 8.04/1.48  fof(f22,axiom,(
% 8.04/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f58,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 8.04/1.48    inference(cnf_transformation,[],[f22])).
% 8.04/1.48  
% 8.04/1.48  fof(f6,axiom,(
% 8.04/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f42,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.04/1.48    inference(cnf_transformation,[],[f6])).
% 8.04/1.48  
% 8.04/1.48  fof(f77,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 8.04/1.48    inference(definition_unfolding,[],[f58,f42,f68])).
% 8.04/1.48  
% 8.04/1.48  fof(f5,axiom,(
% 8.04/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f41,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.04/1.48    inference(cnf_transformation,[],[f5])).
% 8.04/1.48  
% 8.04/1.48  fof(f73,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.04/1.48    inference(definition_unfolding,[],[f41,f42])).
% 8.04/1.48  
% 8.04/1.48  fof(f4,axiom,(
% 8.04/1.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f40,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 8.04/1.48    inference(cnf_transformation,[],[f4])).
% 8.04/1.48  
% 8.04/1.48  fof(f8,axiom,(
% 8.04/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f44,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f8])).
% 8.04/1.48  
% 8.04/1.48  fof(f72,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 8.04/1.48    inference(definition_unfolding,[],[f40,f44])).
% 8.04/1.48  
% 8.04/1.48  fof(f16,axiom,(
% 8.04/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f52,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 8.04/1.48    inference(cnf_transformation,[],[f16])).
% 8.04/1.48  
% 8.04/1.48  fof(f75,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 8.04/1.48    inference(definition_unfolding,[],[f52,f44,f68])).
% 8.04/1.48  
% 8.04/1.48  fof(f7,axiom,(
% 8.04/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f43,plain,(
% 8.04/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.04/1.48    inference(cnf_transformation,[],[f7])).
% 8.04/1.48  
% 8.04/1.48  fof(f2,axiom,(
% 8.04/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f38,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.04/1.48    inference(cnf_transformation,[],[f2])).
% 8.04/1.48  
% 8.04/1.48  fof(f69,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.04/1.48    inference(definition_unfolding,[],[f38,f42])).
% 8.04/1.48  
% 8.04/1.48  fof(f3,axiom,(
% 8.04/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f39,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f3])).
% 8.04/1.48  
% 8.04/1.48  fof(f71,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 8.04/1.48    inference(definition_unfolding,[],[f39,f44])).
% 8.04/1.48  
% 8.04/1.48  fof(f1,axiom,(
% 8.04/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f25,plain,(
% 8.04/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 8.04/1.48    inference(unused_predicate_definition_removal,[],[f1])).
% 8.04/1.48  
% 8.04/1.48  fof(f27,plain,(
% 8.04/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 8.04/1.48    inference(ennf_transformation,[],[f25])).
% 8.04/1.48  
% 8.04/1.48  fof(f37,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 8.04/1.48    inference(cnf_transformation,[],[f27])).
% 8.04/1.48  
% 8.04/1.48  fof(f70,plain,(
% 8.04/1.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 8.04/1.48    inference(definition_unfolding,[],[f37,f42])).
% 8.04/1.48  
% 8.04/1.48  fof(f23,conjecture,(
% 8.04/1.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f24,negated_conjecture,(
% 8.04/1.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 8.04/1.48    inference(negated_conjecture,[],[f23])).
% 8.04/1.48  
% 8.04/1.48  fof(f26,plain,(
% 8.04/1.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 8.04/1.48    inference(pure_predicate_removal,[],[f24])).
% 8.04/1.48  
% 8.04/1.48  fof(f32,plain,(
% 8.04/1.48    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 8.04/1.48    inference(ennf_transformation,[],[f26])).
% 8.04/1.48  
% 8.04/1.48  fof(f33,plain,(
% 8.04/1.48    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 8.04/1.48    inference(flattening,[],[f32])).
% 8.04/1.48  
% 8.04/1.48  fof(f35,plain,(
% 8.04/1.48    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.04/1.48    introduced(choice_axiom,[])).
% 8.04/1.48  
% 8.04/1.48  fof(f34,plain,(
% 8.04/1.48    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 8.04/1.48    introduced(choice_axiom,[])).
% 8.04/1.48  
% 8.04/1.48  fof(f36,plain,(
% 8.04/1.48    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.04/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f35,f34])).
% 8.04/1.48  
% 8.04/1.48  fof(f62,plain,(
% 8.04/1.48    r1_xboole_0(sK1,sK2)),
% 8.04/1.48    inference(cnf_transformation,[],[f36])).
% 8.04/1.48  
% 8.04/1.48  fof(f60,plain,(
% 8.04/1.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.04/1.48    inference(cnf_transformation,[],[f36])).
% 8.04/1.48  
% 8.04/1.48  fof(f59,plain,(
% 8.04/1.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.04/1.48    inference(cnf_transformation,[],[f36])).
% 8.04/1.48  
% 8.04/1.48  fof(f20,axiom,(
% 8.04/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f29,plain,(
% 8.04/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 8.04/1.48    inference(ennf_transformation,[],[f20])).
% 8.04/1.48  
% 8.04/1.48  fof(f30,plain,(
% 8.04/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.04/1.48    inference(flattening,[],[f29])).
% 8.04/1.48  
% 8.04/1.48  fof(f56,plain,(
% 8.04/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.48    inference(cnf_transformation,[],[f30])).
% 8.04/1.48  
% 8.04/1.48  fof(f76,plain,(
% 8.04/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.48    inference(definition_unfolding,[],[f56,f44])).
% 8.04/1.48  
% 8.04/1.48  fof(f61,plain,(
% 8.04/1.48    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 8.04/1.48    inference(cnf_transformation,[],[f36])).
% 8.04/1.48  
% 8.04/1.48  fof(f19,axiom,(
% 8.04/1.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f55,plain,(
% 8.04/1.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 8.04/1.48    inference(cnf_transformation,[],[f19])).
% 8.04/1.48  
% 8.04/1.48  fof(f17,axiom,(
% 8.04/1.48    ! [X0] : k2_subset_1(X0) = X0),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f53,plain,(
% 8.04/1.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 8.04/1.48    inference(cnf_transformation,[],[f17])).
% 8.04/1.48  
% 8.04/1.48  fof(f21,axiom,(
% 8.04/1.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 8.04/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.48  
% 8.04/1.48  fof(f31,plain,(
% 8.04/1.48    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f21])).
% 8.04/1.49  
% 8.04/1.49  fof(f57,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f31])).
% 8.04/1.49  
% 8.04/1.49  fof(f18,axiom,(
% 8.04/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f28,plain,(
% 8.04/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f18])).
% 8.04/1.49  
% 8.04/1.49  fof(f54,plain,(
% 8.04/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f28])).
% 8.04/1.49  
% 8.04/1.49  fof(f63,plain,(
% 8.04/1.49    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 8.04/1.49    inference(cnf_transformation,[],[f36])).
% 8.04/1.49  
% 8.04/1.49  cnf(c_102,plain,
% 8.04/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.04/1.49      theory(equality) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_176,plain,( X0_2 = X0_2 ),theory(equality) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_6,plain,
% 8.04/1.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f74]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(cnf_transformation,[],[f77]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_874,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_6,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f73]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3828,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3838,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_3828,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 8.04/1.49      inference(cnf_transformation,[],[f72]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(cnf_transformation,[],[f75]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_875,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7701,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3,c_875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.04/1.49      inference(cnf_transformation,[],[f43]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7728,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_7701,c_5,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12080,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3838,c_7728]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7708,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_875,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8127,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3838,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_0,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f69]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3829,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3837,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_3829,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3984,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_3837]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_569,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_577,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_569,c_3]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1166,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_577,c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1171,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_1166,c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_516,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_519,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_516,c_3]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1256,plain,
% 8.04/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_1171,c_519]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4023,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_3984,c_13,c_1256,c_3838]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4519,plain,
% 8.04/1.49      ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_4023]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4568,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_4519,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8165,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8127,c_5,c_4568]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12096,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12080,c_8165]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12097,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X1 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_12096,c_7,c_3838,c_8165]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_15641,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3838,c_12097]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_40383,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_15641]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_40495,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_40383,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_2,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f71]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4624,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_4568]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9703,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4624,c_8165]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4742,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_3838]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9706,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_9703,c_4742]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7715,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_875,c_3]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7718,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_7715,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9707,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_9706,c_5,c_1171,c_7718]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3820,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_874]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12927,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_3820,c_13,c_9707]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12946,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_12927]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4503,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_4023]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7711,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_875,c_4503]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7721,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_7711,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9567,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7721,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7714,plain,
% 8.04/1.49      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_875,c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7719,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_7714,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3824,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9434,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7719,c_3824]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9443,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_9434,c_3,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9588,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_9567,c_5,c_9443]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12989,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12946,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_39742,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7708,c_12989]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7935,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7718,c_875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7976,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_7935,c_5,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12240,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_7976]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8132,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4503,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8154,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8132,c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12284,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12240,c_8154,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_38352,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_875,c_12284]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_38585,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_38352,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4675,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4568,c_874]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4682,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_4675,c_13,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11876,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_4682]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11953,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11876,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12443,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_11953,c_875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4552,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4023,c_874]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4559,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_4552,c_13,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8113,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8190,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_8113,c_5,c_4023]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8191,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8190,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12527,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = X0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_12443,c_7,c_4559,c_8191]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12721,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7719,c_12527]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_36412,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7708,c_12721]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12740,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9443,c_12527]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_34517,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7708,c_12740]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12722,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_12527]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_34019,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7708,c_12722]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12067,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_7728]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12120,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12067,c_8154,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_31961,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(k4_xboole_0(X0,X1),X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_12120]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_32023,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_31961,c_4503,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10507,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_9707]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10530,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_10507,c_4503,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12076,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3824,c_7728]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3833,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_3]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3834,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_3833,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8126,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3834,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8166,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8126,c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8192,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8191,c_8166]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12102,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12076,c_8191,c_8192]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_31316,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_10530,c_12102]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12959,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4023,c_12927]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12975,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12959,c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_24114,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_10530,c_12975]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_24328,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_24114,c_1171,c_12989]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8105,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8206,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8105,c_5,c_4023]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_24130,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_10530,c_8206]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7875,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_7718]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_24318,plain,
% 8.04/1.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_24130,c_7875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9851,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3838,c_8191]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9880,plain,
% 8.04/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_9851,c_4568]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_23321,plain,
% 8.04/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4568,c_9880]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3827,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_572,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3839,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_3827,c_13,c_572]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_23703,plain,
% 8.04/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_23321,c_3839]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4793,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3838,c_3838]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4807,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_4793,c_4568]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9426,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7719,c_572]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9455,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_9426,c_7719,c_9443]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_19844,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3838,c_9455]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_19851,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_19844,c_8165]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_22326,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4807,c_19851]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_22414,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_22326,c_4807]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_22360,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4807,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_22377,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_22360,c_4807]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4674,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4568,c_3824]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4683,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_4674,c_3838,c_3839]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_20786,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4568,c_4683]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_21367,plain,
% 8.04/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_20786,c_3839]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_20883,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4683,c_12527]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_20164,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7875,c_19851]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_20556,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_20164,c_7875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11902,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3838,c_4682]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11916,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_11902,c_13,c_3839]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17700,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_6,c_11916]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12713,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_12527]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_16887,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_6,c_12713]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17474,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_16887]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17519,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(light_normalisation,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_17474,c_4503,c_8154,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17115,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_12713]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17231,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(light_normalisation,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_17115,c_4503,c_8154,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17099,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7708,c_12713]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12084,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9443,c_7728]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12087,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12084,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12088,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_12087,c_7,c_9443,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_14860,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_875,c_12088]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_14937,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_14860,c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_15270,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_14937]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_15322,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_15270,c_4503,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11898,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3824,c_4682]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11923,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11898,c_4,c_3838]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13800,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_11923]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13817,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_13800,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13413,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_12975]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13464,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_13413,c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13421,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7719,c_12975]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13458,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_13421,c_13,c_7719]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13433,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_874,c_12975]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13448,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_13433,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1,plain,
% 8.04/1.49      ( ~ r1_xboole_0(X0,X1)
% 8.04/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 8.04/1.49      inference(cnf_transformation,[],[f70]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_15,negated_conjecture,
% 8.04/1.49      ( r1_xboole_0(sK1,sK2) ),
% 8.04/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_119,plain,
% 8.04/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 8.04/1.49      | sK2 != X1
% 8.04/1.49      | sK1 != X0 ),
% 8.04/1.49      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_120,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 8.04/1.49      inference(unflattening,[status(thm)],[c_119]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_515,plain,
% 8.04/1.49      ( k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_120,c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_520,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_515,c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3972,plain,
% 8.04/1.49      ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK2,sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_520,c_3837]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17,negated_conjecture,
% 8.04/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.04/1.49      inference(cnf_transformation,[],[f60]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_298,plain,
% 8.04/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_18,negated_conjecture,
% 8.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.04/1.49      inference(cnf_transformation,[],[f59]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_297,plain,
% 8.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.04/1.49      | k5_xboole_0(X0,k4_xboole_0(X2,X0)) = k4_subset_1(X1,X0,X2) ),
% 8.04/1.49      inference(cnf_transformation,[],[f76]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_300,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 8.04/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 8.04/1.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_458,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k4_xboole_0(X0,sK1))
% 8.04/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_297,c_300]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_629,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_298,c_458]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_16,negated_conjecture,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f61]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_633,plain,
% 8.04/1.49      ( k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_629,c_16]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_635,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_633,c_3]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_682,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(sK1,k2_struct_0(sK0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_635,c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_690,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_682,c_635]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_567,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_120,c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_579,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_567,c_520]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_691,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_690,c_579]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4032,plain,
% 8.04/1.49      ( k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_3972,c_691]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4033,plain,
% 8.04/1.49      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_4032,c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12949,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) = sK2 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4033,c_12927]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4049,plain,
% 8.04/1.49      ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_4033,c_633]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12986,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) = sK2 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12949,c_4049]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7884,plain,
% 8.04/1.49      ( k4_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4033,c_7718]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8005,plain,
% 8.04/1.49      ( k4_xboole_0(sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_7884,c_4049]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_634,plain,
% 8.04/1.49      ( k4_xboole_0(k2_struct_0(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_633,c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_636,plain,
% 8.04/1.49      ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_634,c_520]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3875,plain,
% 8.04/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0))) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_636,c_3824]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8376,plain,
% 8.04/1.49      ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8005,c_3875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8381,plain,
% 8.04/1.49      ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8376,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12728,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_8381,c_12527]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12726,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_636,c_12527]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12732,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3824,c_12527]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12424,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4568,c_11953]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12548,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12424,c_3839]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12224,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7708,c_7976]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12071,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k4_xboole_0(k2_struct_0(sK0),sK2)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_636,c_7728]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_695,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(sK2,sK1),sK1) = k4_xboole_0(sK2,sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_520,c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1650,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))) = k4_xboole_0(k5_xboole_0(sK2,sK1),sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_695,c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1657,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK2,sK1) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_1650,c_695]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3876,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_695,c_3824]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4489,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = sK2 ),
% 8.04/1.49      inference(light_normalisation,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_1657,c_1657,c_3876,c_4033]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8131,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4489,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7878,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_520,c_7718]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8155,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),sK2) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_8131,c_7878]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8156,plain,
% 8.04/1.49      ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8155,c_5,c_1171,c_4049,c_7878]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12113,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12071,c_636,c_8156]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12073,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_8381,c_7728]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8109,plain,
% 8.04/1.49      ( k5_xboole_0(sK1,k4_xboole_0(k2_struct_0(sK0),sK1)) = k5_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_635,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8200,plain,
% 8.04/1.49      ( k5_xboole_0(sK1,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8109,c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12109,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12073,c_4049,c_8200]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12079,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4023,c_7728]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12098,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_12079,c_5,c_4023]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12051,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7708,c_7728]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_2322,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_572]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_2386,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_2322,c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11686,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_2386,c_2386,c_9707]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11703,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_11686]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11809,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11703,c_4503,c_9588]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11444,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_636,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11473,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11444,c_636]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11579,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) = sK1 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_6,c_11473]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11431,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_2,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11486,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11431,c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11436,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_1171,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11481,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11436,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11438,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7718,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11479,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11438,c_7718]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11439,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7719,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11478,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11439,c_7719]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11440,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9707,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11477,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = X1 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11440,c_9707]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11446,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_8381,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11471,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = sK2 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11446,c_8381]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11457,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_9443,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11461,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_11457,c_9443]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11449,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3824,c_4559]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_743,plain,
% 8.04/1.49      ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_636,c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_748,plain,
% 8.04/1.49      ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_743,c_636]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_2056,plain,
% 8.04/1.49      ( k5_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_748,c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11110,plain,
% 8.04/1.49      ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8381,c_2056]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10920,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7875,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10938,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_10920,c_7875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10923,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7875,c_3837]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10932,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0)) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_10923,c_7875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10933,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_10932,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10924,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7875,c_3824]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10931,plain,
% 8.04/1.49      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_10924,c_7875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1268,plain,
% 8.04/1.49      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_1171,c_3]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1763,plain,
% 8.04/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_0,c_1268]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1817,plain,
% 8.04/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_1763,c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7705,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_1817,c_875]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7726,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_7705,c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10727,plain,
% 8.04/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_6,c_7726]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9701,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4568,c_8165]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9710,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_9701,c_3839]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9428,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7719,c_0]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9453,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_9428,c_7719,c_9443]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9435,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7719,c_874]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9444,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_9443,c_9435]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_457,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k5_xboole_0(sK2,k4_xboole_0(X0,sK2))
% 8.04/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_298,c_300]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_587,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_297,c_457]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_589,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,sK1) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_587,c_520]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8444,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8156,c_589]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8405,plain,
% 8.04/1.49      ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_8005,c_3837]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8412,plain,
% 8.04/1.49      ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK2,k1_xboole_0)) = sK1 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_8405,c_636]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8413,plain,
% 8.04/1.49      ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_8412,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8114,plain,
% 8.04/1.49      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_1817,c_7708]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8189,plain,
% 8.04/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_8114,c_5,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10,plain,
% 8.04/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 8.04/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_301,plain,
% 8.04/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8,plain,
% 8.04/1.49      ( k2_subset_1(X0) = X0 ),
% 8.04/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_303,plain,
% 8.04/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_301,c_8]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_459,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X0,X0,X1)
% 8.04/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_303,c_300]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_804,plain,
% 8.04/1.49      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_297,c_459]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8044,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_7708,c_804]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_803,plain,
% 8.04/1.49      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_298,c_459]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8043,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_7708,c_803]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7949,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_7718,c_3837]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7956,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_7949,c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7957,plain,
% 8.04/1.49      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_7956,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4794,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_3838,c_3837]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4806,plain,
% 8.04/1.49      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_4794,c_4568]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4055,plain,
% 8.04/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK2,sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_4033,c_3824]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4063,plain,
% 8.04/1.49      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_4055,c_520,c_691]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_586,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_298,c_457]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_590,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_586,c_572]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4203,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_xboole_0(sK2,k1_xboole_0) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_4063,c_590]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4204,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_4203,c_1171]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3821,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_1171,c_874]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1173,plain,
% 8.04/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_1171,c_577]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3845,plain,
% 8.04/1.49      ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_3821,c_1173]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 8.04/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_299,plain,
% 8.04/1.49      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 8.04/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3315,plain,
% 8.04/1.49      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_303,c_299]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3314,plain,
% 8.04/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_297,c_299]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3313,plain,
% 8.04/1.49      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_298,c_299]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f54]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_302,plain,
% 8.04/1.49      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 8.04/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3190,plain,
% 8.04/1.49      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_303,c_302]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3191,plain,
% 8.04/1.49      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_3190,c_1173]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3189,plain,
% 8.04/1.49      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_297,c_302]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3188,plain,
% 8.04/1.49      ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_298,c_302]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_805,plain,
% 8.04/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_subset_1(X0,X0,X0) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_303,c_459]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_2234,plain,
% 8.04/1.49      ( k4_subset_1(X0,X0,X0) = X0 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_805,c_5,c_805,c_1173]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_630,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_297,c_458]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_632,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_630,c_572]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1026,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_632,c_579,c_632,c_691]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_631,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_303,c_458]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_588,plain,
% 8.04/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_303,c_457]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_14,negated_conjecture,
% 8.04/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 8.04/1.49      inference(cnf_transformation,[],[f63]) ).
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  % SZS output end Saturation for theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  ------                               Statistics
% 8.04/1.49  
% 8.04/1.49  ------ General
% 8.04/1.49  
% 8.04/1.49  abstr_ref_over_cycles:                  0
% 8.04/1.49  abstr_ref_under_cycles:                 0
% 8.04/1.49  gc_basic_clause_elim:                   0
% 8.04/1.49  forced_gc_time:                         0
% 8.04/1.49  parsing_time:                           0.005
% 8.04/1.49  unif_index_cands_time:                  0.
% 8.04/1.49  unif_index_add_time:                    0.
% 8.04/1.49  orderings_time:                         0.
% 8.04/1.49  out_proof_time:                         0.
% 8.04/1.49  total_time:                             0.965
% 8.04/1.49  num_of_symbols:                         49
% 8.04/1.49  num_of_terms:                           23982
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing
% 8.04/1.49  
% 8.04/1.49  num_of_splits:                          0
% 8.04/1.49  num_of_split_atoms:                     0
% 8.04/1.49  num_of_reused_defs:                     0
% 8.04/1.49  num_eq_ax_congr_red:                    36
% 8.04/1.49  num_of_sem_filtered_clauses:            1
% 8.04/1.49  num_of_subtypes:                        0
% 8.04/1.49  monotx_restored_types:                  0
% 8.04/1.49  sat_num_of_epr_types:                   0
% 8.04/1.49  sat_num_of_non_cyclic_types:            0
% 8.04/1.49  sat_guarded_non_collapsed_types:        0
% 8.04/1.49  num_pure_diseq_elim:                    0
% 8.04/1.49  simp_replaced_by:                       0
% 8.04/1.49  res_preprocessed:                       98
% 8.04/1.49  prep_upred:                             0
% 8.04/1.49  prep_unflattend:                        2
% 8.04/1.49  smt_new_axioms:                         0
% 8.04/1.49  pred_elim_cands:                        1
% 8.04/1.49  pred_elim:                              1
% 8.04/1.49  pred_elim_cl:                           1
% 8.04/1.49  pred_elim_cycles:                       3
% 8.04/1.49  merged_defs:                            0
% 8.04/1.49  merged_defs_ncl:                        0
% 8.04/1.49  bin_hyper_res:                          0
% 8.04/1.49  prep_cycles:                            4
% 8.04/1.49  pred_elim_time:                         0.
% 8.04/1.49  splitting_time:                         0.
% 8.04/1.49  sem_filter_time:                        0.
% 8.04/1.49  monotx_time:                            0.
% 8.04/1.49  subtype_inf_time:                       0.
% 8.04/1.49  
% 8.04/1.49  ------ Problem properties
% 8.04/1.49  
% 8.04/1.49  clauses:                                18
% 8.04/1.49  conjectures:                            4
% 8.04/1.49  epr:                                    0
% 8.04/1.49  horn:                                   18
% 8.04/1.49  ground:                                 5
% 8.04/1.49  unary:                                  15
% 8.04/1.49  binary:                                 2
% 8.04/1.49  lits:                                   22
% 8.04/1.49  lits_eq:                                15
% 8.04/1.49  fd_pure:                                0
% 8.04/1.49  fd_pseudo:                              0
% 8.04/1.49  fd_cond:                                0
% 8.04/1.49  fd_pseudo_cond:                         0
% 8.04/1.49  ac_symbols:                             0
% 8.04/1.49  
% 8.04/1.49  ------ Propositional Solver
% 8.04/1.49  
% 8.04/1.49  prop_solver_calls:                      40
% 8.04/1.49  prop_fast_solver_calls:                 833
% 8.04/1.49  smt_solver_calls:                       0
% 8.04/1.49  smt_fast_solver_calls:                  0
% 8.04/1.49  prop_num_of_clauses:                    5408
% 8.04/1.49  prop_preprocess_simplified:             11370
% 8.04/1.49  prop_fo_subsumed:                       0
% 8.04/1.49  prop_solver_time:                       0.
% 8.04/1.49  smt_solver_time:                        0.
% 8.04/1.49  smt_fast_solver_time:                   0.
% 8.04/1.49  prop_fast_solver_time:                  0.
% 8.04/1.49  prop_unsat_core_time:                   0.
% 8.04/1.49  
% 8.04/1.49  ------ QBF
% 8.04/1.49  
% 8.04/1.49  qbf_q_res:                              0
% 8.04/1.49  qbf_num_tautologies:                    0
% 8.04/1.49  qbf_prep_cycles:                        0
% 8.04/1.49  
% 8.04/1.49  ------ BMC1
% 8.04/1.49  
% 8.04/1.49  bmc1_current_bound:                     -1
% 8.04/1.49  bmc1_last_solved_bound:                 -1
% 8.04/1.49  bmc1_unsat_core_size:                   -1
% 8.04/1.49  bmc1_unsat_core_parents_size:           -1
% 8.04/1.49  bmc1_merge_next_fun:                    0
% 8.04/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.04/1.49  
% 8.04/1.49  ------ Instantiation
% 8.04/1.49  
% 8.04/1.49  inst_num_of_clauses:                    3829
% 8.04/1.49  inst_num_in_passive:                    2772
% 8.04/1.49  inst_num_in_active:                     932
% 8.04/1.49  inst_num_in_unprocessed:                125
% 8.04/1.49  inst_num_of_loops:                      1260
% 8.04/1.49  inst_num_of_learning_restarts:          0
% 8.04/1.49  inst_num_moves_active_passive:          319
% 8.04/1.49  inst_lit_activity:                      0
% 8.04/1.49  inst_lit_activity_moves:                1
% 8.04/1.49  inst_num_tautologies:                   0
% 8.04/1.49  inst_num_prop_implied:                  0
% 8.04/1.49  inst_num_existing_simplified:           0
% 8.04/1.49  inst_num_eq_res_simplified:             0
% 8.04/1.49  inst_num_child_elim:                    0
% 8.04/1.49  inst_num_of_dismatching_blockings:      229
% 8.04/1.49  inst_num_of_non_proper_insts:           3745
% 8.04/1.49  inst_num_of_duplicates:                 0
% 8.04/1.49  inst_inst_num_from_inst_to_res:         0
% 8.04/1.49  inst_dismatching_checking_time:         0.
% 8.04/1.49  
% 8.04/1.49  ------ Resolution
% 8.04/1.49  
% 8.04/1.49  res_num_of_clauses:                     0
% 8.04/1.49  res_num_in_passive:                     0
% 8.04/1.49  res_num_in_active:                      0
% 8.04/1.49  res_num_of_loops:                       102
% 8.04/1.49  res_forward_subset_subsumed:            1450
% 8.04/1.49  res_backward_subset_subsumed:           6
% 8.04/1.49  res_forward_subsumed:                   0
% 8.04/1.49  res_backward_subsumed:                  0
% 8.04/1.49  res_forward_subsumption_resolution:     0
% 8.04/1.49  res_backward_subsumption_resolution:    0
% 8.04/1.49  res_clause_to_clause_subsumption:       6346
% 8.04/1.49  res_orphan_elimination:                 0
% 8.04/1.49  res_tautology_del:                      374
% 8.04/1.49  res_num_eq_res_simplified:              0
% 8.04/1.49  res_num_sel_changes:                    0
% 8.04/1.49  res_moves_from_active_to_pass:          0
% 8.04/1.49  
% 8.04/1.49  ------ Superposition
% 8.04/1.49  
% 8.04/1.49  sup_time_total:                         0.
% 8.04/1.49  sup_time_generating:                    0.
% 8.04/1.49  sup_time_sim_full:                      0.
% 8.04/1.49  sup_time_sim_immed:                     0.
% 8.04/1.49  
% 8.04/1.49  sup_num_of_clauses:                     418
% 8.04/1.49  sup_num_in_active:                      156
% 8.04/1.49  sup_num_in_passive:                     262
% 8.04/1.49  sup_num_of_loops:                       250
% 8.04/1.49  sup_fw_superposition:                   16583
% 8.04/1.49  sup_bw_superposition:                   4640
% 8.04/1.49  sup_immediate_simplified:               6776
% 8.04/1.49  sup_given_eliminated:                   2
% 8.04/1.49  comparisons_done:                       0
% 8.04/1.49  comparisons_avoided:                    0
% 8.04/1.49  
% 8.04/1.49  ------ Simplifications
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  sim_fw_subset_subsumed:                 0
% 8.04/1.49  sim_bw_subset_subsumed:                 0
% 8.04/1.49  sim_fw_subsumed:                        445
% 8.04/1.49  sim_bw_subsumed:                        40
% 8.04/1.49  sim_fw_subsumption_res:                 0
% 8.04/1.49  sim_bw_subsumption_res:                 0
% 8.04/1.49  sim_tautology_del:                      0
% 8.04/1.49  sim_eq_tautology_del:                   4324
% 8.04/1.49  sim_eq_res_simp:                        0
% 8.04/1.49  sim_fw_demodulated:                     4860
% 8.04/1.49  sim_bw_demodulated:                     97
% 8.04/1.49  sim_light_normalised:                   3968
% 8.04/1.49  sim_joinable_taut:                      0
% 8.04/1.49  sim_joinable_simp:                      0
% 8.04/1.49  sim_ac_normalised:                      0
% 8.04/1.49  sim_smt_subsumption:                    0
% 8.04/1.49  
%------------------------------------------------------------------------------

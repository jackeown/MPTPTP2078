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
% DateTime   : Thu Dec  3 12:11:13 EST 2020

% Result     : CounterSatisfiable 19.50s
% Output     : Saturation 19.50s
% Verified   : 
% Statistics : Number of formulae       :  794 (98525084 expanded)
%              Number of clauses        :  708 (13129377 expanded)
%              Number of leaves         :   28 (31813369 expanded)
%              Depth                    :   51
%              Number of atoms          :  997 (103447783 expanded)
%              Number of equality atoms :  909 (99343298 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f83,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f52,f75,f75])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f51,f75])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f49,f75])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f45,f49,f51])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f25,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f28,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38])).

fof(f69,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f21,axiom,(
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
    inference(ennf_transformation,[],[f21])).

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

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f51])).

fof(f68,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_161,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_9,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_10,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1283,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_10])).

cnf(c_5803,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1283,c_10])).

cnf(c_6,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5805,plain,
    ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1283,c_6])).

cnf(c_5806,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5805,c_10])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5798,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_1283])).

cnf(c_15,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1282,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_15])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3122,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1282,c_0])).

cnf(c_3125,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3122,c_15])).

cnf(c_3465,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1282,c_3125])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_894,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_1824,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,X0))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_894,c_7])).

cnf(c_1830,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1824,c_894])).

cnf(c_897,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_894,c_4])).

cnf(c_1831,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1830,c_897])).

cnf(c_3121,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1282,c_7])).

cnf(c_3126,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3121,c_15])).

cnf(c_3481,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_3465,c_15,c_1831,c_3126])).

cnf(c_4309,plain,
    ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1282,c_3481])).

cnf(c_3564,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_7,c_3126])).

cnf(c_4363,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_4309,c_15,c_3564])).

cnf(c_902,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_9983,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) ),
    inference(superposition,[status(thm)],[c_4363,c_902])).

cnf(c_4301,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_3481])).

cnf(c_4371,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_4301,c_3481])).

cnf(c_4372,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_4371,c_6])).

cnf(c_5804,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1283,c_4372])).

cnf(c_5807,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_5804,c_10])).

cnf(c_9985,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_5807,c_902])).

cnf(c_11030,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) ),
    inference(light_normalisation,[status(thm)],[c_9985,c_5807])).

cnf(c_3114,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1282,c_15])).

cnf(c_7361,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_5806,c_3114])).

cnf(c_12,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_613,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_617,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_613,c_11])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_5])).

cnf(c_607,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_852,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_617,c_607])).

cnf(c_1834,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1831,c_894])).

cnf(c_7365,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7361,c_852,c_1834])).

cnf(c_7532,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_5807,c_5803])).

cnf(c_7541,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1)) = k5_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(demodulation,[status(thm)],[c_7532,c_7365])).

cnf(c_5023,plain,
    ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1282,c_4363])).

cnf(c_5089,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_5023,c_15])).

cnf(c_10005,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_902,c_5089])).

cnf(c_9943,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1283,c_902])).

cnf(c_7363,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_5806,c_6])).

cnf(c_7364,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_7363,c_1834])).

cnf(c_10133,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_9943,c_10,c_7364])).

cnf(c_10029,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_902,c_6])).

cnf(c_10244,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_10133,c_5803])).

cnf(c_10255,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_10244,c_6])).

cnf(c_10345,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_10029,c_10133,c_10255])).

cnf(c_10346,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_10345,c_7364])).

cnf(c_10018,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_902,c_902])).

cnf(c_10022,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_902,c_5803])).

cnf(c_10354,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10022,c_10133,c_10255,c_10346])).

cnf(c_10358,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_10018,c_10133,c_10255,c_10346,c_10354])).

cnf(c_10359,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_10358,c_7364])).

cnf(c_998,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_10015,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_902,c_998])).

cnf(c_10362,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10015,c_10133,c_10346,c_10354])).

cnf(c_5489,plain,
    ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1282,c_5089])).

cnf(c_5594,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_5489,c_15])).

cnf(c_10023,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_902,c_5594])).

cnf(c_10353,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_10023,c_10133,c_10346])).

cnf(c_10363,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_10362,c_10353])).

cnf(c_10366,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_10363,c_10346])).

cnf(c_10378,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_10005,c_10133,c_10346,c_10359,c_10362,c_10366])).

cnf(c_10379,plain,
    ( k4_xboole_0(X0,X0) = sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_10378])).

cnf(c_11031,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11030,c_7365,c_7541,c_10379])).

cnf(c_10211,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5807,c_10133])).

cnf(c_10889,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_10211,c_3481])).

cnf(c_10890,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_10889,c_7541])).

cnf(c_11032,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11031,c_10890])).

cnf(c_10209,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4363,c_10133])).

cnf(c_10892,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_10209,c_3564])).

cnf(c_11036,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11032,c_10892])).

cnf(c_11064,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,sP1_iProver_split)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11036,c_11032])).

cnf(c_11069,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k5_xboole_0(X0,sP1_iProver_split)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_9983,c_11032,c_11064])).

cnf(c_11070,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k5_xboole_0(X0,sP1_iProver_split)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_11069,c_7])).

cnf(c_999,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_610,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_615,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2313,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_610,c_615])).

cnf(c_2607,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2313,c_0])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2610,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2607,c_8])).

cnf(c_5883,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2610,c_5803])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_614,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1707,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_614])).

cnf(c_2314,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1707,c_615])).

cnf(c_2744,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2314,c_0])).

cnf(c_2747,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_2744,c_8])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_608,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_609,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_612,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1177,plain,
    ( k5_xboole_0(X0,k4_xboole_0(sK2,X0)) = k4_subset_1(u1_struct_0(sK0),X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_612])).

cnf(c_1335,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_608,c_1177])).

cnf(c_19,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1338,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1335,c_19])).

cnf(c_2976,plain,
    ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2747,c_1338])).

cnf(c_5907,plain,
    ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5883,c_2747,c_2976])).

cnf(c_1340,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1338,c_6])).

cnf(c_1487,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)),k2_struct_0(sK0)) = k4_xboole_0(sK2,k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1340,c_6])).

cnf(c_2752,plain,
    ( k4_xboole_0(k5_xboole_0(sK2,sK1),k2_struct_0(sK0)) = k4_xboole_0(sK2,k2_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_2610,c_1487])).

cnf(c_5956,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(sK2,k2_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_5907,c_2752])).

cnf(c_1822,plain,
    ( k4_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1340,c_894])).

cnf(c_850,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,u1_struct_0(sK0))) = sK2 ),
    inference(superposition,[status(thm)],[c_609,c_607])).

cnf(c_1007,plain,
    ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_850,c_7])).

cnf(c_1103,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1007,c_0])).

cnf(c_1105,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_1103,c_1007])).

cnf(c_1008,plain,
    ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_850,c_0])).

cnf(c_1011,plain,
    ( k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1008,c_850])).

cnf(c_1043,plain,
    ( k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1011,c_7])).

cnf(c_1047,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1043,c_1011])).

cnf(c_1106,plain,
    ( k5_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1105,c_1047])).

cnf(c_1862,plain,
    ( k4_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1822,c_1106])).

cnf(c_2748,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2747,c_2314])).

cnf(c_3822,plain,
    ( k4_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1862,c_1862,c_2610,c_2748])).

cnf(c_5957,plain,
    ( k4_xboole_0(sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5907,c_3822])).

cnf(c_5959,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5956,c_5957])).

cnf(c_9971,plain,
    ( k4_xboole_0(k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))),k5_xboole_0(k2_struct_0(sK0),k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    inference(superposition,[status(thm)],[c_5959,c_902])).

cnf(c_11089,plain,
    ( k4_xboole_0(k5_xboole_0(k2_struct_0(sK0),k1_xboole_0),k5_xboole_0(k2_struct_0(sK0),k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_9971,c_5959])).

cnf(c_11090,plain,
    ( sP1_iProver_split = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11089,c_8,c_5959,c_10379])).

cnf(c_11358,plain,
    ( k5_xboole_0(X0,sP1_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_11090,c_8])).

cnf(c_12899,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_11070,c_999,c_11070,c_11358])).

cnf(c_5882,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_1282,c_5803])).

cnf(c_5910,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(demodulation,[status(thm)],[c_5882,c_15])).

cnf(c_12956,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0)) ),
    inference(superposition,[status(thm)],[c_12899,c_5910])).

cnf(c_12964,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_12899,c_1282])).

cnf(c_5066,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_4363,c_3114])).

cnf(c_5070,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5066,c_7])).

cnf(c_5067,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_4363,c_1282])).

cnf(c_5071,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_5070,c_5067])).

cnf(c_12967,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_12964,c_5071])).

cnf(c_12981,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_12956,c_12899,c_12967])).

cnf(c_12982,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12981,c_7,c_11358])).

cnf(c_13064,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_12982])).

cnf(c_17603,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5798,c_13064])).

cnf(c_17629,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5806,c_17603])).

cnf(c_17670,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_17629,c_7365])).

cnf(c_78202,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5803,c_17670])).

cnf(c_83292,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_78202])).

cnf(c_12909,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_6,c_12899])).

cnf(c_13658,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_5807,c_12909])).

cnf(c_13894,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),sP1_iProver_split),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_13658,c_11032])).

cnf(c_10238,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_10133,c_998])).

cnf(c_893,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_905,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_893,c_894,c_897])).

cnf(c_10402,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_10379,c_10133])).

cnf(c_10851,plain,
    ( k4_xboole_0(X0,sP1_iProver_split) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10238,c_905,c_10402])).

cnf(c_13085,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5806,c_12982])).

cnf(c_13124,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_13085,c_7365])).

cnf(c_13895,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_13894,c_6,c_7365,c_10851,c_11032,c_13124])).

cnf(c_3113,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_1282])).

cnf(c_13709,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),sP1_iProver_split)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_12909,c_12982])).

cnf(c_13739,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_12909,c_3114])).

cnf(c_996,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_1001,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_996,c_6])).

cnf(c_13742,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_13739,c_1001])).

cnf(c_13782,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_13709,c_13742])).

cnf(c_10010,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_902,c_3481])).

cnf(c_10179,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_10133])).

cnf(c_901,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_903,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_901,c_6])).

cnf(c_10654,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_5806,c_903])).

cnf(c_10799,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_10654,c_1834,c_10379])).

cnf(c_10800,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_10799,c_998,c_10379])).

cnf(c_10852,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_10851,c_10800])).

cnf(c_10930,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_10179,c_10852])).

cnf(c_10963,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10015,c_10851,c_10930])).

cnf(c_10964,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_10963,c_10402])).

cnf(c_10226,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0) ),
    inference(superposition,[status(thm)],[c_10133,c_5807])).

cnf(c_10863,plain,
    ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) = k4_xboole_0(sP1_iProver_split,X1) ),
    inference(light_normalisation,[status(thm)],[c_10226,c_10379,c_10402])).

cnf(c_10967,plain,
    ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(sP1_iProver_split,X1) ),
    inference(demodulation,[status(thm)],[c_10964,c_10863])).

cnf(c_10981,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(sP1_iProver_split,X1) ),
    inference(demodulation,[status(thm)],[c_10010,c_10930,c_10967])).

cnf(c_10982,plain,
    ( k4_xboole_0(sP1_iProver_split,X0) = k4_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_10981,c_10402])).

cnf(c_10983,plain,
    ( k4_xboole_0(sP1_iProver_split,X0) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_10982,c_10379])).

cnf(c_10224,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0)) ),
    inference(superposition,[status(thm)],[c_10133,c_5910])).

cnf(c_10866,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1))) = k5_xboole_0(X1,k4_xboole_0(sP1_iProver_split,X1)) ),
    inference(light_normalisation,[status(thm)],[c_10224,c_10379,c_10402])).

cnf(c_10867,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,k4_xboole_0(sP1_iProver_split,X1)) ),
    inference(demodulation,[status(thm)],[c_10866,c_6])).

cnf(c_10993,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_10983,c_10867])).

cnf(c_13783,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = k5_xboole_0(X1,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_13782,c_10993])).

cnf(c_13784,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_13783,c_11358])).

cnf(c_17345,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0 ),
    inference(demodulation,[status(thm)],[c_3113,c_15,c_13784])).

cnf(c_17356,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5910,c_17345])).

cnf(c_3123,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))),X0) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1282,c_6])).

cnf(c_3124,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_3123,c_15])).

cnf(c_13088,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_3124,c_12982])).

cnf(c_7776,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_3124,c_1282])).

cnf(c_7778,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(demodulation,[status(thm)],[c_7776,c_15])).

cnf(c_13120,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_13088,c_7778,c_11032])).

cnf(c_10190,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1282,c_10133])).

cnf(c_10913,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_10190,c_10379])).

cnf(c_10914,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_10913,c_15])).

cnf(c_12717,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))),X0)) ),
    inference(superposition,[status(thm)],[c_10914,c_5910])).

cnf(c_12774,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0))) = k5_xboole_0(X0,k4_xboole_0(sP1_iProver_split,X0)) ),
    inference(demodulation,[status(thm)],[c_12717,c_10914])).

cnf(c_12775,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12774,c_3124,c_7778,c_10983,c_11358])).

cnf(c_12776,plain,
    ( k5_xboole_0(sP1_iProver_split,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_12775,c_10851,c_10914])).

cnf(c_13121,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_13120,c_10851,c_10914,c_12776])).

cnf(c_17449,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_17356,c_13121])).

cnf(c_64107,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_17449])).

cnf(c_68824,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_6,c_64107])).

cnf(c_68922,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_68824,c_6])).

cnf(c_70541,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13895,c_68922])).

cnf(c_70744,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_70541,c_7365,c_10964])).

cnf(c_81929,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3126,c_70744])).

cnf(c_13079,plain,
    ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k4_xboole_0(X1,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_1282,c_12982])).

cnf(c_13127,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X1 ),
    inference(light_normalisation,[status(thm)],[c_13079,c_15])).

cnf(c_13128,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_13127,c_3126])).

cnf(c_81978,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_81929,c_13128])).

cnf(c_82011,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3114,c_81978])).

cnf(c_34236,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3126,c_13121])).

cnf(c_10707,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_5089,c_903])).

cnf(c_10733,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_10707,c_998,c_3126])).

cnf(c_11039,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),sP1_iProver_split)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_11032,c_10733])).

cnf(c_11056,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_11039,c_10851])).

cnf(c_11057,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11056,c_10379])).

cnf(c_34379,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_34236,c_11057])).

cnf(c_75675,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_10930,c_34379])).

cnf(c_17360,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_17345])).

cnf(c_21841,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_17360,c_15])).

cnf(c_21842,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_21841,c_10930])).

cnf(c_76357,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_75675,c_10930,c_21842])).

cnf(c_23846,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13784,c_17603])).

cnf(c_23944,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_23846,c_6])).

cnf(c_24213,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_23944])).

cnf(c_80855,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(sP1_iProver_split,k5_xboole_0(sP1_iProver_split,k5_xboole_0(X1,k4_xboole_0(X0,X1)))))) = k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_76357,c_24213])).

cnf(c_10006,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_902,c_4372])).

cnf(c_11001,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_10006,c_10930,c_10964,c_10983])).

cnf(c_5135,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0) ),
    inference(superposition,[status(thm)],[c_6,c_4372])).

cnf(c_11002,plain,
    ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_11001,c_5135,c_10402])).

cnf(c_80918,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(sP1_iProver_split,k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(sP1_iProver_split,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_80855,c_11002,c_21842])).

cnf(c_12947,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_12899,c_3481])).

cnf(c_12990,plain,
    ( k4_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_12947,c_12899])).

cnf(c_1284,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_897])).

cnf(c_11357,plain,
    ( k4_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11090,c_1284])).

cnf(c_12991,plain,
    ( k4_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_12990,c_11357])).

cnf(c_23427,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_12991,c_1283])).

cnf(c_23534,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_23427,c_10,c_11358])).

cnf(c_24180,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,sP1_iProver_split))) ),
    inference(superposition,[status(thm)],[c_10914,c_23534])).

cnf(c_24209,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_24180,c_10851,c_10914])).

cnf(c_80919,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(sP1_iProver_split,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_80918,c_12776,c_24209])).

cnf(c_17386,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_13895,c_17345])).

cnf(c_17419,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_17386,c_15,c_10964])).

cnf(c_17420,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_17419,c_13895])).

cnf(c_31389,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3114,c_17420])).

cnf(c_7353,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5806,c_998])).

cnf(c_7377,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_7353,c_5806,c_7365])).

cnf(c_32624,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3126,c_7377])).

cnf(c_32667,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_32624,c_13128])).

cnf(c_74245,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(sP1_iProver_split,k4_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_31389,c_32667])).

cnf(c_3589,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_3126,c_3125])).

cnf(c_13102,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X0) ),
    inference(superposition,[status(thm)],[c_12982,c_4372])).

cnf(c_13113,plain,
    ( k4_xboole_0(sP1_iProver_split,k4_xboole_0(X0,X1)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_13102,c_10983,c_11032])).

cnf(c_75134,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_74245,c_3589,c_13113])).

cnf(c_64481,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_5806,c_17449])).

cnf(c_64553,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_64481,c_15,c_5806])).

cnf(c_69412,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_31389,c_64553])).

cnf(c_13075,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_12899,c_12982])).

cnf(c_13130,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_13075,c_12967])).

cnf(c_69420,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_69412,c_13130])).

cnf(c_17387,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),sP1_iProver_split))) = X0 ),
    inference(superposition,[status(thm)],[c_10914,c_17345])).

cnf(c_12735,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_10914,c_5803])).

cnf(c_12746,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),sP1_iProver_split) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_12735,c_3124])).

cnf(c_12747,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),sP1_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_12746,c_11032,c_11358])).

cnf(c_17418,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_17387,c_12747])).

cnf(c_69421,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_69420,c_12967,c_17418])).

cnf(c_2754,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2610,c_1340])).

cnf(c_3422,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0))) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_2754,c_3114])).

cnf(c_6082,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5957,c_3422])).

cnf(c_2743,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2314,c_7])).

cnf(c_2758,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2743,c_2747])).

cnf(c_6083,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_6082,c_2758])).

cnf(c_68827,plain,
    ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_6083,c_64107])).

cnf(c_68919,plain,
    ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_68827,c_6083])).

cnf(c_68832,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13784,c_64107])).

cnf(c_68915,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_68832,c_13784])).

cnf(c_68842,plain,
    ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_2754,c_64107])).

cnf(c_68907,plain,
    ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_68842,c_2754])).

cnf(c_68846,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_5806,c_64107])).

cnf(c_68904,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_68846,c_5806])).

cnf(c_2862,plain,
    ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2748,c_1007])).

cnf(c_11347,plain,
    ( k4_xboole_0(sK2,u1_struct_0(sK0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11090,c_2862])).

cnf(c_1838,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_998])).

cnf(c_1855,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1838,c_6])).

cnf(c_14843,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_1855,c_1855,c_13784])).

cnf(c_14858,plain,
    ( k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split),k4_xboole_0(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_11347,c_14843])).

cnf(c_15001,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_14858,c_998,c_11358])).

cnf(c_68852,plain,
    ( k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_15001,c_64107])).

cnf(c_68899,plain,
    ( k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_68852,c_15001])).

cnf(c_2611,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2610,c_2313])).

cnf(c_851,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_608,c_607])).

cnf(c_1038,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_851,c_7])).

cnf(c_2616,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2611,c_1038])).

cnf(c_8282,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2616,c_5910])).

cnf(c_2606,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2313,c_7])).

cnf(c_2622,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2606,c_2610])).

cnf(c_8392,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
    inference(light_normalisation,[status(thm)],[c_8282,c_2622])).

cnf(c_8763,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_8392,c_6])).

cnf(c_7536,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5807,c_6])).

cnf(c_7537,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1)),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7536,c_7365])).

cnf(c_7543,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_7541,c_7537])).

cnf(c_8765,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_8763,c_7543])).

cnf(c_68853,plain,
    ( k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_8765,c_64107])).

cnf(c_68898,plain,
    ( k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_68853,c_8765])).

cnf(c_68877,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_31389,c_64107])).

cnf(c_64512,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_31389,c_17449])).

cnf(c_64521,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_64512,c_15,c_12967])).

cnf(c_68884,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_68877,c_12967,c_64521])).

cnf(c_64487,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_15001,c_17449])).

cnf(c_64548,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_64487,c_15001])).

cnf(c_64488,plain,
    ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_8765,c_17449])).

cnf(c_64547,plain,
    ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_64488,c_8765])).

cnf(c_64475,plain,
    ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1282,c_17449])).

cnf(c_64559,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_64475,c_15])).

cnf(c_30195,plain,
    ( k1_setfam_1(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_11002,c_17345])).

cnf(c_30302,plain,
    ( k1_setfam_1(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_30195,c_10964])).

cnf(c_61181,plain,
    ( k1_setfam_1(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_5594,c_30302])).

cnf(c_61218,plain,
    ( k1_setfam_1(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,X0)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_61181,c_11057,c_11358])).

cnf(c_62349,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sP1_iProver_split)) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_9,c_61218])).

cnf(c_17613,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_17603])).

cnf(c_17679,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_17613,c_13784])).

cnf(c_37293,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_13784,c_17679])).

cnf(c_13070,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_12982])).

cnf(c_37397,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_37293,c_13070,c_13124])).

cnf(c_55584,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5803,c_37397])).

cnf(c_55109,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_37397])).

cnf(c_17619,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_12899,c_17603])).

cnf(c_17676,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_17619,c_12967])).

cnf(c_54997,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_5594,c_17676])).

cnf(c_5542,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_5089,c_1282])).

cnf(c_5547,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5542,c_5071])).

cnf(c_5753,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_5594,c_1282])).

cnf(c_5521,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_5089,c_3114])).

cnf(c_3119,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1282,c_0])).

cnf(c_3128,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3119,c_15,c_998])).

cnf(c_5564,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_5521,c_3128])).

cnf(c_5522,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_5089,c_1282])).

cnf(c_5567,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_5564,c_5522])).

cnf(c_5757,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5753,c_5567])).

cnf(c_55045,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_54997,c_5547,c_5757])).

cnf(c_13105,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_12982,c_1283])).

cnf(c_33725,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5806,c_13105])).

cnf(c_54336,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5803,c_33725])).

cnf(c_24553,plain,
    ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1283,c_23944])).

cnf(c_24789,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_24553,c_10])).

cnf(c_27774,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_13784,c_24789])).

cnf(c_14698,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_5803,c_13895])).

cnf(c_27889,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_27774,c_10964,c_13124,c_14698])).

cnf(c_53071,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_27889])).

cnf(c_7355,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_5806,c_0])).

cnf(c_7375,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_7355,c_5806,c_7365])).

cnf(c_50179,plain,
    ( k5_xboole_0(k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))),sP1_iProver_split) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_31389,c_7375])).

cnf(c_50655,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_50179,c_13130])).

cnf(c_24650,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),sP1_iProver_split)) = k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_12991,c_23944])).

cnf(c_24658,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_24650,c_12967,c_13130])).

cnf(c_47687,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),sP1_iProver_split)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_5594,c_24658])).

cnf(c_47732,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_47687,c_5547,c_5757])).

cnf(c_24175,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_5594,c_23534])).

cnf(c_24811,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_24175,c_5547,c_5757])).

cnf(c_42808,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_5594,c_24811])).

cnf(c_43163,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_42808,c_3128,c_11057])).

cnf(c_42469,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_10930,c_3114])).

cnf(c_42473,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_42469,c_10930])).

cnf(c_12931,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_5594,c_12899])).

cnf(c_13009,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_12931,c_5757])).

cnf(c_21736,plain,
    ( k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1283,c_17360])).

cnf(c_21989,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_21736,c_10])).

cnf(c_23047,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split))) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_13895,c_21989])).

cnf(c_23085,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_23047,c_7365,c_10964,c_21989])).

cnf(c_39040,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_13009,c_23085])).

cnf(c_39148,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k5_xboole_0(sP1_iProver_split,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_39040,c_13009])).

cnf(c_39094,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_13009,c_5803])).

cnf(c_39111,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_39094,c_13009])).

cnf(c_39098,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_13009,c_3114])).

cnf(c_39103,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_39098,c_13009])).

cnf(c_25306,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_5594,c_24213])).

cnf(c_25358,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_25306,c_3126,c_11057,c_11358])).

cnf(c_25359,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_25358,c_10,c_11057,c_11358])).

cnf(c_25761,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5806,c_25359])).

cnf(c_35524,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5803,c_25761])).

cnf(c_34552,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5594,c_13128])).

cnf(c_34593,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_34552,c_3128,c_11057])).

cnf(c_10247,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_10133,c_3125])).

cnf(c_10832,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_10247,c_6])).

cnf(c_10833,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_10832,c_852])).

cnf(c_32702,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_13784,c_10833])).

cnf(c_32781,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_32702,c_13124,c_14698])).

cnf(c_29826,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_5803,c_10402])).

cnf(c_31805,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_29826,c_1283])).

cnf(c_31902,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_31805,c_10964])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_616,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3120,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_616])).

cnf(c_3127,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3120,c_15])).

cnf(c_11343,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_3127])).

cnf(c_19917,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_11343])).

cnf(c_28905,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_19917])).

cnf(c_29024,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28905,c_15])).

cnf(c_2945,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_616])).

cnf(c_13248,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2945,c_11090])).

cnf(c_13313,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_13248])).

cnf(c_13337,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13313,c_11057,c_11358])).

cnf(c_28778,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != sP1_iProver_split
    | r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_13337])).

cnf(c_28897,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28778,c_15])).

cnf(c_25755,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_1282,c_25359])).

cnf(c_25794,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_25755,c_15])).

cnf(c_27264,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3126,c_25794])).

cnf(c_25768,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_15001,c_25359])).

cnf(c_25285,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_13784,c_24213])).

cnf(c_25390,plain,
    ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_25285,c_13070,c_13124,c_14698])).

cnf(c_25268,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5803,c_24213])).

cnf(c_24568,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_13784,c_23944])).

cnf(c_24771,plain,
    ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_24568,c_13070,c_13124,c_14698])).

cnf(c_21414,plain,
    ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_17360])).

cnf(c_2944,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_616])).

cnf(c_3115,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_2944])).

cnf(c_3133,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3115,c_15])).

cnf(c_11315,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_3133])).

cnf(c_20665,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_11315])).

cnf(c_20761,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20665,c_5564])).

cnf(c_4397,plain,
    ( k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_3127])).

cnf(c_4418,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4397,c_15,c_3126])).

cnf(c_4844,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_4418])).

cnf(c_4881,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4844,c_15])).

cnf(c_11314,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_4881])).

cnf(c_20535,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_11314])).

cnf(c_20631,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20535,c_5564])).

cnf(c_20555,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_11314])).

cnf(c_20607,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20555,c_5547])).

cnf(c_19912,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) != sP1_iProver_split
    | r1_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5806,c_11343])).

cnf(c_19949,plain,
    ( sP1_iProver_split != X0
    | r1_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19912,c_7365])).

cnf(c_11340,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_4418])).

cnf(c_19812,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5806,c_11340])).

cnf(c_19868,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19812,c_5806])).

cnf(c_19257,plain,
    ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_15001,c_17603])).

cnf(c_5878,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2862,c_5803])).

cnf(c_5913,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_5878,c_8])).

cnf(c_14702,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_5913,c_13895])).

cnf(c_19015,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sP1_iProver_split)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_14702,c_3125])).

cnf(c_19016,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_14702,c_3114])).

cnf(c_19020,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sP1_iProver_split) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(light_normalisation,[status(thm)],[c_19016,c_15001])).

cnf(c_19021,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(demodulation,[status(thm)],[c_19015,c_19020])).

cnf(c_19022,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_19021,c_15001])).

cnf(c_18689,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_8765,c_0])).

cnf(c_18732,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_18689,c_8765])).

cnf(c_18690,plain,
    ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_8765,c_17603])).

cnf(c_17625,plain,
    ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2754,c_17603])).

cnf(c_17673,plain,
    ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_17625,c_6083])).

cnf(c_18081,plain,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_9,c_17673])).

cnf(c_17616,plain,
    ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2))) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_6083,c_17603])).

cnf(c_17678,plain,
    ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_17616,c_2754])).

cnf(c_17860,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_9,c_17678])).

cnf(c_17618,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_897,c_17603])).

cnf(c_17677,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sP1_iProver_split)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_17618,c_10379])).

cnf(c_17637,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5594,c_17603])).

cnf(c_17663,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_17637,c_5757])).

cnf(c_17640,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,sP1_iProver_split))) = X0 ),
    inference(superposition,[status(thm)],[c_10914,c_17603])).

cnf(c_17661,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_17640,c_10851])).

cnf(c_17609,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_3114,c_17603])).

cnf(c_17371,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_2747,c_17345])).

cnf(c_17437,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_17371,c_2976])).

cnf(c_17373,plain,
    ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK2,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2610,c_17345])).

cnf(c_17435,plain,
    ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_17373,c_5907])).

cnf(c_17385,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4372,c_17345])).

cnf(c_17421,plain,
    ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_17385,c_10964,c_11032])).

cnf(c_8762,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_8392,c_4372])).

cnf(c_8766,plain,
    ( k4_xboole_0(sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_8762,c_8765])).

cnf(c_8767,plain,
    ( k4_xboole_0(sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8766,c_2616])).

cnf(c_8773,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8767,c_1283])).

cnf(c_8816,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
    inference(demodulation,[status(thm)],[c_8773,c_8,c_10])).

cnf(c_11348,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11090,c_2616])).

cnf(c_12521,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(sK1,sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_11348,c_5910])).

cnf(c_12525,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_11348,c_4372])).

cnf(c_9949,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)))) ),
    inference(superposition,[status(thm)],[c_8392,c_902])).

cnf(c_11145,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_9949,c_11032])).

cnf(c_8787,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),sK1)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8767,c_5803])).

cnf(c_8796,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),sK1)) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
    inference(demodulation,[status(thm)],[c_8787,c_8])).

cnf(c_9015,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_8796,c_6])).

cnf(c_7715,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(sK1,k1_xboole_0)),u1_struct_0(sK0)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2616,c_3124])).

cnf(c_7836,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),u1_struct_0(sK0)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_7715,c_2622])).

cnf(c_8681,plain,
    ( k4_xboole_0(k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_7836,c_6])).

cnf(c_8682,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_8681,c_8392])).

cnf(c_9016,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9015,c_8682,c_8767])).

cnf(c_11146,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11145,c_8765,c_9016])).

cnf(c_12532,plain,
    ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_12525,c_11090,c_11146])).

cnf(c_12538,plain,
    ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(sK1,sP1_iProver_split)) = k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_12521,c_12532])).

cnf(c_11354,plain,
    ( k4_xboole_0(sK1,sP1_iProver_split) = sK1 ),
    inference(demodulation,[status(thm)],[c_11090,c_2622])).

cnf(c_12539,plain,
    ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) = k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_12538,c_11354])).

cnf(c_12540,plain,
    ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_12539,c_11358])).

cnf(c_16489,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_8816,c_8816,c_12540])).

cnf(c_8281,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2862,c_5910])).

cnf(c_8393,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_8281,c_2758])).

cnf(c_16307,plain,
    ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) = k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_8393,c_8393,c_14702])).

cnf(c_16308,plain,
    ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_16307,c_11358,c_13124])).

cnf(c_4391,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(u1_struct_0(sK0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2862,c_3127])).

cnf(c_4422,plain,
    ( sK2 != k1_xboole_0
    | r1_xboole_0(u1_struct_0(sK0),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4391,c_2758])).

cnf(c_15726,plain,
    ( sP1_iProver_split != sK2
    | r1_xboole_0(u1_struct_0(sK0),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4422,c_11090])).

cnf(c_3351,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2862,c_616])).

cnf(c_3362,plain,
    ( sK2 != k1_xboole_0
    | r1_xboole_0(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3351,c_2758])).

cnf(c_15722,plain,
    ( sP1_iProver_split != sK2
    | r1_xboole_0(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3362,c_11090])).

cnf(c_1844,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)) = k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1340,c_998])).

cnf(c_1850,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1844,c_1340])).

cnf(c_2749,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_2610,c_1850])).

cnf(c_14413,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_6083,c_2749])).

cnf(c_13288,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5807,c_13248])).

cnf(c_13372,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X1) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13288,c_7365,c_7541])).

cnf(c_13373,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13372,c_5806,c_5807,c_7541,c_13124])).

cnf(c_13374,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13373,c_13124])).

cnf(c_13309,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,X0)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5806,c_13248])).

cnf(c_13343,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)),k4_xboole_0(X1,X0)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13309,c_1834])).

cnf(c_13344,plain,
    ( sP1_iProver_split != X0
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13343,c_7365,c_10379,c_10964])).

cnf(c_13315,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3481,c_13248])).

cnf(c_10705,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3481,c_903])).

cnf(c_10735,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_10705,c_3481])).

cnf(c_10736,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_10735,c_998])).

cnf(c_11048,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split),sP1_iProver_split)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11032,c_10736])).

cnf(c_11052,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11048,c_10851])).

cnf(c_11053,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11052,c_10851])).

cnf(c_13335,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split),sP1_iProver_split) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13315,c_11032,c_11053])).

cnf(c_13336,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13335,c_10851,c_11358])).

cnf(c_13318,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5807,c_13248])).

cnf(c_13330,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),sP1_iProver_split) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13318,c_11032])).

cnf(c_13331,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13330,c_7365,c_10851,c_13124])).

cnf(c_13319,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0)),sP1_iProver_split) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10914,c_13248])).

cnf(c_12730,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0),k4_xboole_0(X0,sP1_iProver_split))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_10914,c_10914])).

cnf(c_12754,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X0)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_12730,c_3124,c_10851])).

cnf(c_12755,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k5_xboole_0(sP1_iProver_split,X0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_12754,c_11032])).

cnf(c_12777,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_12776,c_12755])).

cnf(c_13329,plain,
    ( sP1_iProver_split != X0
    | r1_xboole_0(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13319,c_10851,c_11358,c_12777,c_13121])).

cnf(c_13320,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1))),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1))),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7836,c_13248])).

cnf(c_8786,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k1_xboole_0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_8767,c_5806])).

cnf(c_8797,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k1_xboole_0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8786,c_8767])).

cnf(c_8798,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8797,c_8,c_8682])).

cnf(c_11319,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11090,c_8798])).

cnf(c_13327,plain,
    ( k4_xboole_0(k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split),sP1_iProver_split) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split),u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13320,c_11319,c_12532,c_12540])).

cnf(c_13328,plain,
    ( u1_struct_0(sK0) != sP1_iProver_split
    | r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13327,c_10851,c_11358])).

cnf(c_6088,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(k2_struct_0(sK0),sK2))) = k4_xboole_0(k4_xboole_0(sK2,k2_struct_0(sK0)),sK2) ),
    inference(superposition,[status(thm)],[c_5957,c_4372])).

cnf(c_6122,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(k2_struct_0(sK0),sK2))) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_6088,c_5957])).

cnf(c_4324,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k5_xboole_0(sK2,sK1)),sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3822,c_3481])).

cnf(c_4346,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4324,c_1284,c_3822])).

cnf(c_6123,plain,
    ( k4_xboole_0(k1_xboole_0,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6122,c_2754,c_4346,c_5907])).

cnf(c_11335,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_struct_0(sK0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11090,c_6123])).

cnf(c_13321,plain,
    ( k4_xboole_0(k5_xboole_0(sP1_iProver_split,k4_xboole_0(k2_struct_0(sK0),sP1_iProver_split)),sP1_iProver_split) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(sP1_iProver_split,k4_xboole_0(k2_struct_0(sK0),sP1_iProver_split)),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11335,c_13248])).

cnf(c_6248,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6123,c_5803])).

cnf(c_6251,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6123,c_3125])).

cnf(c_6254,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_xboole_0) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6251,c_1284])).

cnf(c_6255,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_6254,c_8])).

cnf(c_6261,plain,
    ( k5_xboole_0(k1_xboole_0,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6248,c_6255])).

cnf(c_6262,plain,
    ( k5_xboole_0(k1_xboole_0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_6261,c_8])).

cnf(c_11332,plain,
    ( k5_xboole_0(sP1_iProver_split,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_11090,c_6262])).

cnf(c_11333,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sP1_iProver_split) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_11090,c_6255])).

cnf(c_13326,plain,
    ( k2_struct_0(sK0) != sP1_iProver_split
    | r1_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13321,c_11332,c_11333])).

cnf(c_4400,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != k1_xboole_0
    | r1_xboole_0(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2754,c_3127])).

cnf(c_11341,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != sP1_iProver_split
    | r1_xboole_0(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_4400])).

cnf(c_11360,plain,
    ( sP1_iProver_split != sK2
    | r1_xboole_0(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11341,c_6083])).

cnf(c_2951,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != k1_xboole_0
    | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2754,c_616])).

cnf(c_11342,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != sP1_iProver_split
    | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_2951])).

cnf(c_11359,plain,
    ( sP1_iProver_split != sK2
    | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11342,c_6083])).

cnf(c_11356,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = sP1_iProver_split
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_615])).

cnf(c_11352,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_616])).

cnf(c_11351,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(X0,k4_xboole_0(X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_2944])).

cnf(c_1814,plain,
    ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1338,c_894])).

cnf(c_1169,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1038,c_0])).

cnf(c_1171,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_1169,c_1038])).

cnf(c_1039,plain,
    ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_851,c_0])).

cnf(c_1042,plain,
    ( k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1039,c_851])).

cnf(c_1097,plain,
    ( k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_1042,c_7])).

cnf(c_1101,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1097,c_1042])).

cnf(c_1172,plain,
    ( k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1171,c_1101])).

cnf(c_1869,plain,
    ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1814,c_1172])).

cnf(c_2615,plain,
    ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2611,c_1869])).

cnf(c_11349,plain,
    ( k4_xboole_0(sK1,k2_struct_0(sK0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11090,c_2615])).

cnf(c_3045,plain,
    ( sK1 != k1_xboole_0
    | r1_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2754,c_2944])).

cnf(c_3052,plain,
    ( sK1 != k1_xboole_0
    | r1_xboole_0(k2_struct_0(sK0),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3045,c_2754])).

cnf(c_11345,plain,
    ( sP1_iProver_split != sK1
    | r1_xboole_0(k2_struct_0(sK0),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_3052])).

cnf(c_11336,plain,
    ( k4_xboole_0(sK2,k2_struct_0(sK0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_11090,c_5957])).

cnf(c_3253,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2615,c_616])).

cnf(c_3264,plain,
    ( sK1 != k1_xboole_0
    | r1_xboole_0(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3253,c_2622])).

cnf(c_11328,plain,
    ( sP1_iProver_split != sK1
    | r1_xboole_0(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_3264])).

cnf(c_3336,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2616,c_616])).

cnf(c_3347,plain,
    ( sK1 != k1_xboole_0
    | r1_xboole_0(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3336,c_2622])).

cnf(c_11325,plain,
    ( sP1_iProver_split != sK1
    | r1_xboole_0(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_3347])).

cnf(c_4392,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(u1_struct_0(sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2616,c_3127])).

cnf(c_4421,plain,
    ( sK1 != k1_xboole_0
    | r1_xboole_0(u1_struct_0(sK0),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4392,c_2622])).

cnf(c_11324,plain,
    ( sP1_iProver_split != sK1
    | r1_xboole_0(u1_struct_0(sK0),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_4421])).

cnf(c_3038,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2944])).

cnf(c_3059,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3038,c_6])).

cnf(c_11318,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_3059])).

cnf(c_4836,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_4418])).

cnf(c_4888,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4836,c_6])).

cnf(c_11313,plain,
    ( k4_xboole_0(X0,X1) != sP1_iProver_split
    | r1_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_4888])).

cnf(c_9996,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_3133])).

cnf(c_11012,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9996,c_10851,c_10930])).

cnf(c_11013,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11012,c_10402])).

cnf(c_11092,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_11013])).

cnf(c_11111,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11092,c_10851])).

cnf(c_10009,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_3127])).

cnf(c_10998,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10009,c_10402])).

cnf(c_11093,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_10998])).

cnf(c_11110,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11093,c_10851])).

cnf(c_10014,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_616])).

cnf(c_10978,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10014,c_10402])).

cnf(c_11094,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_10978])).

cnf(c_11109,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) != sP1_iProver_split
    | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11094,c_10851])).

cnf(c_10232,plain,
    ( k4_xboole_0(X0,X0) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10133,c_4418])).

cnf(c_10858,plain,
    ( sP1_iProver_split != k1_xboole_0
    | r1_xboole_0(sP1_iProver_split,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10232,c_10379,c_10402])).

cnf(c_11099,plain,
    ( sP1_iProver_split != sP1_iProver_split
    | r1_xboole_0(sP1_iProver_split,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_10858])).

cnf(c_11106,plain,
    ( r1_xboole_0(sP1_iProver_split,X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11099])).

cnf(c_10236,plain,
    ( k4_xboole_0(X0,X0) != k1_xboole_0
    | r1_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10133,c_2944])).

cnf(c_10855,plain,
    ( sP1_iProver_split != k1_xboole_0
    | r1_xboole_0(X0,sP1_iProver_split) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10236,c_10379,c_10402])).

cnf(c_11101,plain,
    ( sP1_iProver_split != sP1_iProver_split
    | r1_xboole_0(X0,sP1_iProver_split) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_10855])).

cnf(c_11105,plain,
    ( r1_xboole_0(X0,sP1_iProver_split) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11101])).

cnf(c_10237,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) != k1_xboole_0
    | r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10133,c_616])).

cnf(c_10854,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10237,c_852])).

cnf(c_11102,plain,
    ( sP1_iProver_split != X0
    | r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_10854])).

cnf(c_10233,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10133,c_3127])).

cnf(c_10857,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10233,c_852])).

cnf(c_11100,plain,
    ( sP1_iProver_split != X0
    | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11090,c_10857])).

cnf(c_10241,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_10133,c_5910])).

cnf(c_10845,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))) ),
    inference(light_normalisation,[status(thm)],[c_10241,c_6,c_4372])).

cnf(c_10846,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(demodulation,[status(thm)],[c_10845,c_852])).

cnf(c_11044,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(demodulation,[status(thm)],[c_11032,c_10846])).

cnf(c_9998,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_902,c_5910])).

cnf(c_11009,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_9998,c_10851,c_10930,c_10964,c_11002])).

cnf(c_11010,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_11009,c_10402])).

cnf(c_10019,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_902,c_5910])).

cnf(c_10231,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0) ),
    inference(superposition,[status(thm)],[c_10133,c_4372])).

cnf(c_10859,plain,
    ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(sP1_iProver_split,X0) ),
    inference(light_normalisation,[status(thm)],[c_10231,c_10379,c_10402])).

cnf(c_10860,plain,
    ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(sP1_iProver_split,X0) ),
    inference(demodulation,[status(thm)],[c_10859,c_6])).

cnf(c_10955,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(sP1_iProver_split,X1)) ),
    inference(demodulation,[status(thm)],[c_10019,c_10860,c_10930])).

cnf(c_10956,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(sP1_iProver_split,X0)) = k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_10955,c_10402])).

cnf(c_10986,plain,
    ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_10983,c_10956])).

cnf(c_10997,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_10986,c_10851,c_10964])).

cnf(c_10229,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_10133,c_1283])).

cnf(c_10862,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_10229,c_10379])).

cnf(c_10974,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10964,c_10862])).

cnf(c_10949,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_10022,c_10930])).

cnf(c_10950,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_10949,c_10402])).

cnf(c_10028,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_902,c_3114])).

cnf(c_10938,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10028,c_10851,c_10930])).

cnf(c_10939,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_10938,c_10402])).

cnf(c_10629,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_998,c_903])).

cnf(c_10827,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,sP1_iProver_split)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_10629,c_852,c_10379])).

cnf(c_10853,plain,
    ( k5_xboole_0(X0,X0) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_10851,c_10827])).

cnf(c_10838,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_10244,c_6])).

cnf(c_10839,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10838,c_10379])).

cnf(c_7362,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5806,c_1282])).

cnf(c_7366,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_7365,c_7362])).

cnf(c_6101,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_5957,c_3125])).

cnf(c_6105,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_6101,c_2754,c_2758])).

cnf(c_1178,plain,
    ( k5_xboole_0(X0,k4_xboole_0(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_608,c_612])).

cnf(c_1491,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_609,c_1178])).

cnf(c_2753,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_2610,c_1491])).

cnf(c_5958,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_5907,c_2753])).

cnf(c_1179,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_612])).

cnf(c_5457,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_608,c_1179])).

cnf(c_5879,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2616,c_5803])).

cnf(c_5912,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_5879,c_8])).

cnf(c_5955,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5457,c_5457,c_5912])).

cnf(c_5456,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_609,c_1179])).

cnf(c_5918,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5456,c_5456,c_5913])).

cnf(c_5458,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_617,c_1179])).

cnf(c_5459,plain,
    ( k4_subset_1(X0,X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5458,c_905])).

cnf(c_1493,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_617,c_1178])).

cnf(c_1494,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_1493,c_1038])).

cnf(c_4764,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1494,c_1494,c_2611])).

cnf(c_4765,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4764,c_8,c_1494])).

cnf(c_1336,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_617,c_1177])).

cnf(c_1337,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK2,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1336,c_1007])).

cnf(c_4710,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1337,c_1337,c_2748])).

cnf(c_4711,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4710,c_8,c_1337])).

cnf(c_3459,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_2862,c_3125])).

cnf(c_3485,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(light_normalisation,[status(thm)],[c_3459,c_2758])).

cnf(c_3460,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_2616,c_3125])).

cnf(c_3484,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_3460,c_2622])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_611,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3074,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_617,c_611])).

cnf(c_3073,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_608,c_611])).

cnf(c_3072,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_609,c_611])).

cnf(c_1492,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_608,c_1178])).

cnf(c_1098,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_1042,c_0])).

cnf(c_1100,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1098,c_1042])).

cnf(c_1495,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1492,c_1100])).

cnf(c_1334,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_609,c_1177])).

cnf(c_1044,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_1011,c_0])).

cnf(c_1046,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1044,c_1011])).

cnf(c_1339,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1334,c_1046])).

cnf(c_17,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f70])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:36:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.50/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.50/2.99  
% 19.50/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.50/2.99  
% 19.50/2.99  ------  iProver source info
% 19.50/2.99  
% 19.50/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.50/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.50/2.99  git: non_committed_changes: false
% 19.50/2.99  git: last_make_outside_of_git: false
% 19.50/2.99  
% 19.50/2.99  ------ 
% 19.50/2.99  
% 19.50/2.99  ------ Input Options
% 19.50/2.99  
% 19.50/2.99  --out_options                           all
% 19.50/2.99  --tptp_safe_out                         true
% 19.50/2.99  --problem_path                          ""
% 19.50/2.99  --include_path                          ""
% 19.50/2.99  --clausifier                            res/vclausify_rel
% 19.50/2.99  --clausifier_options                    ""
% 19.50/2.99  --stdin                                 false
% 19.50/2.99  --stats_out                             all
% 19.50/2.99  
% 19.50/2.99  ------ General Options
% 19.50/2.99  
% 19.50/2.99  --fof                                   false
% 19.50/2.99  --time_out_real                         305.
% 19.50/2.99  --time_out_virtual                      -1.
% 19.50/2.99  --symbol_type_check                     false
% 19.50/2.99  --clausify_out                          false
% 19.50/2.99  --sig_cnt_out                           false
% 19.50/2.99  --trig_cnt_out                          false
% 19.50/2.99  --trig_cnt_out_tolerance                1.
% 19.50/2.99  --trig_cnt_out_sk_spl                   false
% 19.50/2.99  --abstr_cl_out                          false
% 19.50/2.99  
% 19.50/2.99  ------ Global Options
% 19.50/2.99  
% 19.50/2.99  --schedule                              default
% 19.50/2.99  --add_important_lit                     false
% 19.50/2.99  --prop_solver_per_cl                    1000
% 19.50/2.99  --min_unsat_core                        false
% 19.50/2.99  --soft_assumptions                      false
% 19.50/2.99  --soft_lemma_size                       3
% 19.50/2.99  --prop_impl_unit_size                   0
% 19.50/2.99  --prop_impl_unit                        []
% 19.50/2.99  --share_sel_clauses                     true
% 19.50/2.99  --reset_solvers                         false
% 19.50/2.99  --bc_imp_inh                            [conj_cone]
% 19.50/2.99  --conj_cone_tolerance                   3.
% 19.50/2.99  --extra_neg_conj                        none
% 19.50/2.99  --large_theory_mode                     true
% 19.50/2.99  --prolific_symb_bound                   200
% 19.50/2.99  --lt_threshold                          2000
% 19.50/2.99  --clause_weak_htbl                      true
% 19.50/2.99  --gc_record_bc_elim                     false
% 19.50/2.99  
% 19.50/2.99  ------ Preprocessing Options
% 19.50/2.99  
% 19.50/2.99  --preprocessing_flag                    true
% 19.50/2.99  --time_out_prep_mult                    0.1
% 19.50/2.99  --splitting_mode                        input
% 19.50/2.99  --splitting_grd                         true
% 19.50/2.99  --splitting_cvd                         false
% 19.50/2.99  --splitting_cvd_svl                     false
% 19.50/2.99  --splitting_nvd                         32
% 19.50/2.99  --sub_typing                            true
% 19.50/2.99  --prep_gs_sim                           true
% 19.50/2.99  --prep_unflatten                        true
% 19.50/2.99  --prep_res_sim                          true
% 19.50/2.99  --prep_upred                            true
% 19.50/2.99  --prep_sem_filter                       exhaustive
% 19.50/2.99  --prep_sem_filter_out                   false
% 19.50/2.99  --pred_elim                             true
% 19.50/2.99  --res_sim_input                         true
% 19.50/2.99  --eq_ax_congr_red                       true
% 19.50/2.99  --pure_diseq_elim                       true
% 19.50/2.99  --brand_transform                       false
% 19.50/2.99  --non_eq_to_eq                          false
% 19.50/2.99  --prep_def_merge                        true
% 19.50/2.99  --prep_def_merge_prop_impl              false
% 19.50/2.99  --prep_def_merge_mbd                    true
% 19.50/2.99  --prep_def_merge_tr_red                 false
% 19.50/2.99  --prep_def_merge_tr_cl                  false
% 19.50/2.99  --smt_preprocessing                     true
% 19.50/2.99  --smt_ac_axioms                         fast
% 19.50/2.99  --preprocessed_out                      false
% 19.50/2.99  --preprocessed_stats                    false
% 19.50/2.99  
% 19.50/2.99  ------ Abstraction refinement Options
% 19.50/2.99  
% 19.50/2.99  --abstr_ref                             []
% 19.50/2.99  --abstr_ref_prep                        false
% 19.50/2.99  --abstr_ref_until_sat                   false
% 19.50/2.99  --abstr_ref_sig_restrict                funpre
% 19.50/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.50/2.99  --abstr_ref_under                       []
% 19.50/2.99  
% 19.50/2.99  ------ SAT Options
% 19.50/2.99  
% 19.50/2.99  --sat_mode                              false
% 19.50/2.99  --sat_fm_restart_options                ""
% 19.50/2.99  --sat_gr_def                            false
% 19.50/2.99  --sat_epr_types                         true
% 19.50/2.99  --sat_non_cyclic_types                  false
% 19.50/2.99  --sat_finite_models                     false
% 19.50/2.99  --sat_fm_lemmas                         false
% 19.50/2.99  --sat_fm_prep                           false
% 19.50/2.99  --sat_fm_uc_incr                        true
% 19.50/2.99  --sat_out_model                         small
% 19.50/2.99  --sat_out_clauses                       false
% 19.50/2.99  
% 19.50/2.99  ------ QBF Options
% 19.50/2.99  
% 19.50/2.99  --qbf_mode                              false
% 19.50/2.99  --qbf_elim_univ                         false
% 19.50/2.99  --qbf_dom_inst                          none
% 19.50/2.99  --qbf_dom_pre_inst                      false
% 19.50/2.99  --qbf_sk_in                             false
% 19.50/2.99  --qbf_pred_elim                         true
% 19.50/2.99  --qbf_split                             512
% 19.50/2.99  
% 19.50/2.99  ------ BMC1 Options
% 19.50/2.99  
% 19.50/2.99  --bmc1_incremental                      false
% 19.50/2.99  --bmc1_axioms                           reachable_all
% 19.50/2.99  --bmc1_min_bound                        0
% 19.50/2.99  --bmc1_max_bound                        -1
% 19.50/2.99  --bmc1_max_bound_default                -1
% 19.50/2.99  --bmc1_symbol_reachability              true
% 19.50/2.99  --bmc1_property_lemmas                  false
% 19.50/2.99  --bmc1_k_induction                      false
% 19.50/2.99  --bmc1_non_equiv_states                 false
% 19.50/2.99  --bmc1_deadlock                         false
% 19.50/2.99  --bmc1_ucm                              false
% 19.50/2.99  --bmc1_add_unsat_core                   none
% 19.50/2.99  --bmc1_unsat_core_children              false
% 19.50/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.50/2.99  --bmc1_out_stat                         full
% 19.50/2.99  --bmc1_ground_init                      false
% 19.50/2.99  --bmc1_pre_inst_next_state              false
% 19.50/2.99  --bmc1_pre_inst_state                   false
% 19.50/2.99  --bmc1_pre_inst_reach_state             false
% 19.50/2.99  --bmc1_out_unsat_core                   false
% 19.50/2.99  --bmc1_aig_witness_out                  false
% 19.50/2.99  --bmc1_verbose                          false
% 19.50/2.99  --bmc1_dump_clauses_tptp                false
% 19.50/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.50/2.99  --bmc1_dump_file                        -
% 19.50/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.50/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.50/2.99  --bmc1_ucm_extend_mode                  1
% 19.50/2.99  --bmc1_ucm_init_mode                    2
% 19.50/2.99  --bmc1_ucm_cone_mode                    none
% 19.50/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.50/2.99  --bmc1_ucm_relax_model                  4
% 19.50/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.50/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.50/2.99  --bmc1_ucm_layered_model                none
% 19.50/2.99  --bmc1_ucm_max_lemma_size               10
% 19.50/2.99  
% 19.50/2.99  ------ AIG Options
% 19.50/2.99  
% 19.50/2.99  --aig_mode                              false
% 19.50/2.99  
% 19.50/2.99  ------ Instantiation Options
% 19.50/2.99  
% 19.50/2.99  --instantiation_flag                    true
% 19.50/2.99  --inst_sos_flag                         true
% 19.50/2.99  --inst_sos_phase                        true
% 19.50/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.50/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.50/2.99  --inst_lit_sel_side                     num_symb
% 19.50/2.99  --inst_solver_per_active                1400
% 19.50/2.99  --inst_solver_calls_frac                1.
% 19.50/2.99  --inst_passive_queue_type               priority_queues
% 19.50/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.50/2.99  --inst_passive_queues_freq              [25;2]
% 19.50/2.99  --inst_dismatching                      true
% 19.50/2.99  --inst_eager_unprocessed_to_passive     true
% 19.50/2.99  --inst_prop_sim_given                   true
% 19.50/2.99  --inst_prop_sim_new                     false
% 19.50/2.99  --inst_subs_new                         false
% 19.50/2.99  --inst_eq_res_simp                      false
% 19.50/2.99  --inst_subs_given                       false
% 19.50/2.99  --inst_orphan_elimination               true
% 19.50/2.99  --inst_learning_loop_flag               true
% 19.50/2.99  --inst_learning_start                   3000
% 19.50/2.99  --inst_learning_factor                  2
% 19.50/2.99  --inst_start_prop_sim_after_learn       3
% 19.50/2.99  --inst_sel_renew                        solver
% 19.50/2.99  --inst_lit_activity_flag                true
% 19.50/2.99  --inst_restr_to_given                   false
% 19.50/2.99  --inst_activity_threshold               500
% 19.50/2.99  --inst_out_proof                        true
% 19.50/2.99  
% 19.50/2.99  ------ Resolution Options
% 19.50/2.99  
% 19.50/2.99  --resolution_flag                       true
% 19.50/2.99  --res_lit_sel                           adaptive
% 19.50/2.99  --res_lit_sel_side                      none
% 19.50/2.99  --res_ordering                          kbo
% 19.50/2.99  --res_to_prop_solver                    active
% 19.50/2.99  --res_prop_simpl_new                    false
% 19.50/2.99  --res_prop_simpl_given                  true
% 19.50/2.99  --res_passive_queue_type                priority_queues
% 19.50/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.50/2.99  --res_passive_queues_freq               [15;5]
% 19.50/2.99  --res_forward_subs                      full
% 19.50/2.99  --res_backward_subs                     full
% 19.50/2.99  --res_forward_subs_resolution           true
% 19.50/2.99  --res_backward_subs_resolution          true
% 19.50/2.99  --res_orphan_elimination                true
% 19.50/2.99  --res_time_limit                        2.
% 19.50/2.99  --res_out_proof                         true
% 19.50/2.99  
% 19.50/2.99  ------ Superposition Options
% 19.50/2.99  
% 19.50/2.99  --superposition_flag                    true
% 19.50/2.99  --sup_passive_queue_type                priority_queues
% 19.50/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.50/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.50/2.99  --demod_completeness_check              fast
% 19.50/2.99  --demod_use_ground                      true
% 19.50/2.99  --sup_to_prop_solver                    passive
% 19.50/2.99  --sup_prop_simpl_new                    true
% 19.50/2.99  --sup_prop_simpl_given                  true
% 19.50/2.99  --sup_fun_splitting                     true
% 19.50/2.99  --sup_smt_interval                      50000
% 19.50/2.99  
% 19.50/2.99  ------ Superposition Simplification Setup
% 19.50/2.99  
% 19.50/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.50/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.50/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.50/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.50/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.50/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.50/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.50/2.99  --sup_immed_triv                        [TrivRules]
% 19.50/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.50/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.50/2.99  --sup_immed_bw_main                     []
% 19.50/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.50/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.50/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.50/2.99  --sup_input_bw                          []
% 19.50/2.99  
% 19.50/2.99  ------ Combination Options
% 19.50/2.99  
% 19.50/2.99  --comb_res_mult                         3
% 19.50/2.99  --comb_sup_mult                         2
% 19.50/2.99  --comb_inst_mult                        10
% 19.50/2.99  
% 19.50/2.99  ------ Debug Options
% 19.50/2.99  
% 19.50/2.99  --dbg_backtrace                         false
% 19.50/2.99  --dbg_dump_prop_clauses                 false
% 19.50/2.99  --dbg_dump_prop_clauses_file            -
% 19.50/2.99  --dbg_out_stat                          false
% 19.50/2.99  ------ Parsing...
% 19.50/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.50/2.99  
% 19.50/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.50/2.99  
% 19.50/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.50/2.99  
% 19.50/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.50/2.99  ------ Proving...
% 19.50/2.99  ------ Problem Properties 
% 19.50/2.99  
% 19.50/2.99  
% 19.50/2.99  clauses                                 21
% 19.50/2.99  conjectures                             5
% 19.50/2.99  EPR                                     2
% 19.50/2.99  Horn                                    21
% 19.50/2.99  unary                                   15
% 19.50/2.99  binary                                  5
% 19.50/2.99  lits                                    28
% 19.50/2.99  lits eq                                 16
% 19.50/2.99  fd_pure                                 0
% 19.50/2.99  fd_pseudo                               0
% 19.50/2.99  fd_cond                                 0
% 19.50/2.99  fd_pseudo_cond                          0
% 19.50/2.99  AC symbols                              0
% 19.50/2.99  
% 19.50/2.99  ------ Schedule dynamic 5 is on 
% 19.50/2.99  
% 19.50/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.50/2.99  
% 19.50/2.99  
% 19.50/2.99  ------ 
% 19.50/2.99  Current options:
% 19.50/2.99  ------ 
% 19.50/2.99  
% 19.50/2.99  ------ Input Options
% 19.50/2.99  
% 19.50/2.99  --out_options                           all
% 19.50/2.99  --tptp_safe_out                         true
% 19.50/2.99  --problem_path                          ""
% 19.50/2.99  --include_path                          ""
% 19.50/2.99  --clausifier                            res/vclausify_rel
% 19.50/2.99  --clausifier_options                    ""
% 19.50/2.99  --stdin                                 false
% 19.50/2.99  --stats_out                             all
% 19.50/2.99  
% 19.50/2.99  ------ General Options
% 19.50/2.99  
% 19.50/2.99  --fof                                   false
% 19.50/2.99  --time_out_real                         305.
% 19.50/2.99  --time_out_virtual                      -1.
% 19.50/2.99  --symbol_type_check                     false
% 19.50/2.99  --clausify_out                          false
% 19.50/2.99  --sig_cnt_out                           false
% 19.50/2.99  --trig_cnt_out                          false
% 19.50/2.99  --trig_cnt_out_tolerance                1.
% 19.50/2.99  --trig_cnt_out_sk_spl                   false
% 19.50/2.99  --abstr_cl_out                          false
% 19.50/2.99  
% 19.50/2.99  ------ Global Options
% 19.50/2.99  
% 19.50/2.99  --schedule                              default
% 19.50/2.99  --add_important_lit                     false
% 19.50/2.99  --prop_solver_per_cl                    1000
% 19.50/2.99  --min_unsat_core                        false
% 19.50/2.99  --soft_assumptions                      false
% 19.50/2.99  --soft_lemma_size                       3
% 19.50/2.99  --prop_impl_unit_size                   0
% 19.50/2.99  --prop_impl_unit                        []
% 19.50/2.99  --share_sel_clauses                     true
% 19.50/2.99  --reset_solvers                         false
% 19.50/2.99  --bc_imp_inh                            [conj_cone]
% 19.50/2.99  --conj_cone_tolerance                   3.
% 19.50/2.99  --extra_neg_conj                        none
% 19.50/2.99  --large_theory_mode                     true
% 19.50/2.99  --prolific_symb_bound                   200
% 19.50/2.99  --lt_threshold                          2000
% 19.50/2.99  --clause_weak_htbl                      true
% 19.50/2.99  --gc_record_bc_elim                     false
% 19.50/2.99  
% 19.50/2.99  ------ Preprocessing Options
% 19.50/2.99  
% 19.50/2.99  --preprocessing_flag                    true
% 19.50/2.99  --time_out_prep_mult                    0.1
% 19.50/2.99  --splitting_mode                        input
% 19.50/2.99  --splitting_grd                         true
% 19.50/2.99  --splitting_cvd                         false
% 19.50/2.99  --splitting_cvd_svl                     false
% 19.50/2.99  --splitting_nvd                         32
% 19.50/2.99  --sub_typing                            true
% 19.50/2.99  --prep_gs_sim                           true
% 19.50/2.99  --prep_unflatten                        true
% 19.50/2.99  --prep_res_sim                          true
% 19.50/2.99  --prep_upred                            true
% 19.50/2.99  --prep_sem_filter                       exhaustive
% 19.50/2.99  --prep_sem_filter_out                   false
% 19.50/2.99  --pred_elim                             true
% 19.50/2.99  --res_sim_input                         true
% 19.50/2.99  --eq_ax_congr_red                       true
% 19.50/2.99  --pure_diseq_elim                       true
% 19.50/2.99  --brand_transform                       false
% 19.50/2.99  --non_eq_to_eq                          false
% 19.50/2.99  --prep_def_merge                        true
% 19.50/2.99  --prep_def_merge_prop_impl              false
% 19.50/2.99  --prep_def_merge_mbd                    true
% 19.50/2.99  --prep_def_merge_tr_red                 false
% 19.50/2.99  --prep_def_merge_tr_cl                  false
% 19.50/2.99  --smt_preprocessing                     true
% 19.50/2.99  --smt_ac_axioms                         fast
% 19.50/2.99  --preprocessed_out                      false
% 19.50/2.99  --preprocessed_stats                    false
% 19.50/2.99  
% 19.50/2.99  ------ Abstraction refinement Options
% 19.50/2.99  
% 19.50/2.99  --abstr_ref                             []
% 19.50/2.99  --abstr_ref_prep                        false
% 19.50/2.99  --abstr_ref_until_sat                   false
% 19.50/2.99  --abstr_ref_sig_restrict                funpre
% 19.50/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.50/2.99  --abstr_ref_under                       []
% 19.50/2.99  
% 19.50/2.99  ------ SAT Options
% 19.50/2.99  
% 19.50/2.99  --sat_mode                              false
% 19.50/2.99  --sat_fm_restart_options                ""
% 19.50/2.99  --sat_gr_def                            false
% 19.50/2.99  --sat_epr_types                         true
% 19.50/2.99  --sat_non_cyclic_types                  false
% 19.50/2.99  --sat_finite_models                     false
% 19.50/2.99  --sat_fm_lemmas                         false
% 19.50/2.99  --sat_fm_prep                           false
% 19.50/2.99  --sat_fm_uc_incr                        true
% 19.50/2.99  --sat_out_model                         small
% 19.50/2.99  --sat_out_clauses                       false
% 19.50/2.99  
% 19.50/2.99  ------ QBF Options
% 19.50/2.99  
% 19.50/2.99  --qbf_mode                              false
% 19.50/2.99  --qbf_elim_univ                         false
% 19.50/2.99  --qbf_dom_inst                          none
% 19.50/2.99  --qbf_dom_pre_inst                      false
% 19.50/2.99  --qbf_sk_in                             false
% 19.50/2.99  --qbf_pred_elim                         true
% 19.50/2.99  --qbf_split                             512
% 19.50/2.99  
% 19.50/2.99  ------ BMC1 Options
% 19.50/2.99  
% 19.50/2.99  --bmc1_incremental                      false
% 19.50/2.99  --bmc1_axioms                           reachable_all
% 19.50/2.99  --bmc1_min_bound                        0
% 19.50/2.99  --bmc1_max_bound                        -1
% 19.50/2.99  --bmc1_max_bound_default                -1
% 19.50/2.99  --bmc1_symbol_reachability              true
% 19.50/2.99  --bmc1_property_lemmas                  false
% 19.50/2.99  --bmc1_k_induction                      false
% 19.50/2.99  --bmc1_non_equiv_states                 false
% 19.50/2.99  --bmc1_deadlock                         false
% 19.50/2.99  --bmc1_ucm                              false
% 19.50/2.99  --bmc1_add_unsat_core                   none
% 19.50/2.99  --bmc1_unsat_core_children              false
% 19.50/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.50/2.99  --bmc1_out_stat                         full
% 19.50/2.99  --bmc1_ground_init                      false
% 19.50/2.99  --bmc1_pre_inst_next_state              false
% 19.50/2.99  --bmc1_pre_inst_state                   false
% 19.50/2.99  --bmc1_pre_inst_reach_state             false
% 19.50/2.99  --bmc1_out_unsat_core                   false
% 19.50/2.99  --bmc1_aig_witness_out                  false
% 19.50/2.99  --bmc1_verbose                          false
% 19.50/2.99  --bmc1_dump_clauses_tptp                false
% 19.50/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.50/2.99  --bmc1_dump_file                        -
% 19.50/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.50/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.50/2.99  --bmc1_ucm_extend_mode                  1
% 19.50/2.99  --bmc1_ucm_init_mode                    2
% 19.50/2.99  --bmc1_ucm_cone_mode                    none
% 19.50/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.50/2.99  --bmc1_ucm_relax_model                  4
% 19.50/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.50/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.50/2.99  --bmc1_ucm_layered_model                none
% 19.50/2.99  --bmc1_ucm_max_lemma_size               10
% 19.50/2.99  
% 19.50/2.99  ------ AIG Options
% 19.50/2.99  
% 19.50/2.99  --aig_mode                              false
% 19.50/2.99  
% 19.50/2.99  ------ Instantiation Options
% 19.50/2.99  
% 19.50/2.99  --instantiation_flag                    true
% 19.50/2.99  --inst_sos_flag                         true
% 19.50/2.99  --inst_sos_phase                        true
% 19.50/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.50/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.50/2.99  --inst_lit_sel_side                     none
% 19.50/2.99  --inst_solver_per_active                1400
% 19.50/2.99  --inst_solver_calls_frac                1.
% 19.50/2.99  --inst_passive_queue_type               priority_queues
% 19.50/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.50/2.99  --inst_passive_queues_freq              [25;2]
% 19.50/2.99  --inst_dismatching                      true
% 19.50/2.99  --inst_eager_unprocessed_to_passive     true
% 19.50/2.99  --inst_prop_sim_given                   true
% 19.50/2.99  --inst_prop_sim_new                     false
% 19.50/2.99  --inst_subs_new                         false
% 19.50/2.99  --inst_eq_res_simp                      false
% 19.50/2.99  --inst_subs_given                       false
% 19.50/2.99  --inst_orphan_elimination               true
% 19.50/2.99  --inst_learning_loop_flag               true
% 19.50/2.99  --inst_learning_start                   3000
% 19.50/2.99  --inst_learning_factor                  2
% 19.50/2.99  --inst_start_prop_sim_after_learn       3
% 19.50/2.99  --inst_sel_renew                        solver
% 19.50/2.99  --inst_lit_activity_flag                true
% 19.50/2.99  --inst_restr_to_given                   false
% 19.50/2.99  --inst_activity_threshold               500
% 19.50/2.99  --inst_out_proof                        true
% 19.50/2.99  
% 19.50/2.99  ------ Resolution Options
% 19.50/2.99  
% 19.50/2.99  --resolution_flag                       false
% 19.50/2.99  --res_lit_sel                           adaptive
% 19.50/2.99  --res_lit_sel_side                      none
% 19.50/2.99  --res_ordering                          kbo
% 19.50/2.99  --res_to_prop_solver                    active
% 19.50/2.99  --res_prop_simpl_new                    false
% 19.50/2.99  --res_prop_simpl_given                  true
% 19.50/2.99  --res_passive_queue_type                priority_queues
% 19.50/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.50/2.99  --res_passive_queues_freq               [15;5]
% 19.50/2.99  --res_forward_subs                      full
% 19.50/2.99  --res_backward_subs                     full
% 19.50/2.99  --res_forward_subs_resolution           true
% 19.50/2.99  --res_backward_subs_resolution          true
% 19.50/2.99  --res_orphan_elimination                true
% 19.50/2.99  --res_time_limit                        2.
% 19.50/2.99  --res_out_proof                         true
% 19.50/2.99  
% 19.50/2.99  ------ Superposition Options
% 19.50/2.99  
% 19.50/2.99  --superposition_flag                    true
% 19.50/2.99  --sup_passive_queue_type                priority_queues
% 19.50/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.50/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.50/2.99  --demod_completeness_check              fast
% 19.50/2.99  --demod_use_ground                      true
% 19.50/2.99  --sup_to_prop_solver                    passive
% 19.50/2.99  --sup_prop_simpl_new                    true
% 19.50/2.99  --sup_prop_simpl_given                  true
% 19.50/2.99  --sup_fun_splitting                     true
% 19.50/2.99  --sup_smt_interval                      50000
% 19.50/2.99  
% 19.50/2.99  ------ Superposition Simplification Setup
% 19.50/2.99  
% 19.50/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.50/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.50/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.50/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.50/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.50/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.50/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.50/2.99  --sup_immed_triv                        [TrivRules]
% 19.50/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.50/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.50/2.99  --sup_immed_bw_main                     []
% 19.50/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.50/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.50/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.50/2.99  --sup_input_bw                          []
% 19.50/2.99  
% 19.50/2.99  ------ Combination Options
% 19.50/2.99  
% 19.50/2.99  --comb_res_mult                         3
% 19.50/2.99  --comb_sup_mult                         2
% 19.50/2.99  --comb_inst_mult                        10
% 19.50/2.99  
% 19.50/2.99  ------ Debug Options
% 19.50/2.99  
% 19.50/2.99  --dbg_backtrace                         false
% 19.50/2.99  --dbg_dump_prop_clauses                 false
% 19.50/2.99  --dbg_dump_prop_clauses_file            -
% 19.50/2.99  --dbg_out_stat                          false
% 19.50/2.99  
% 19.50/2.99  
% 19.50/2.99  
% 19.50/2.99  
% 19.50/2.99  ------ Proving...
% 19.50/2.99  
% 19.50/2.99  
% 19.50/2.99  % SZS status CounterSatisfiable for theBenchmark.p
% 19.50/2.99  
% 19.50/2.99  % SZS output start Saturation for theBenchmark.p
% 19.50/2.99  
% 19.50/2.99  fof(f11,axiom,(
% 19.50/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f52,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f11])).
% 19.50/2.99  
% 19.50/2.99  fof(f12,axiom,(
% 19.50/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f53,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f12])).
% 19.50/2.99  
% 19.50/2.99  fof(f13,axiom,(
% 19.50/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f54,plain,(
% 19.50/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f13])).
% 19.50/2.99  
% 19.50/2.99  fof(f14,axiom,(
% 19.50/2.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f55,plain,(
% 19.50/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f14])).
% 19.50/2.99  
% 19.50/2.99  fof(f15,axiom,(
% 19.50/2.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f56,plain,(
% 19.50/2.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f15])).
% 19.50/2.99  
% 19.50/2.99  fof(f16,axiom,(
% 19.50/2.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f57,plain,(
% 19.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f16])).
% 19.50/2.99  
% 19.50/2.99  fof(f17,axiom,(
% 19.50/2.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f58,plain,(
% 19.50/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f17])).
% 19.50/2.99  
% 19.50/2.99  fof(f71,plain,(
% 19.50/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f57,f58])).
% 19.50/2.99  
% 19.50/2.99  fof(f72,plain,(
% 19.50/2.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f56,f71])).
% 19.50/2.99  
% 19.50/2.99  fof(f73,plain,(
% 19.50/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f55,f72])).
% 19.50/2.99  
% 19.50/2.99  fof(f74,plain,(
% 19.50/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f54,f73])).
% 19.50/2.99  
% 19.50/2.99  fof(f75,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f53,f74])).
% 19.50/2.99  
% 19.50/2.99  fof(f83,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f52,f75,f75])).
% 19.50/2.99  
% 19.50/2.99  fof(f18,axiom,(
% 19.50/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f59,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f18])).
% 19.50/2.99  
% 19.50/2.99  fof(f10,axiom,(
% 19.50/2.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f51,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f10])).
% 19.50/2.99  
% 19.50/2.99  fof(f84,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.50/2.99    inference(definition_unfolding,[],[f59,f51,f75])).
% 19.50/2.99  
% 19.50/2.99  fof(f6,axiom,(
% 19.50/2.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f47,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f6])).
% 19.50/2.99  
% 19.50/2.99  fof(f81,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f47,f51])).
% 19.50/2.99  
% 19.50/2.99  fof(f7,axiom,(
% 19.50/2.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f48,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f7])).
% 19.50/2.99  
% 19.50/2.99  fof(f8,axiom,(
% 19.50/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f49,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f8])).
% 19.50/2.99  
% 19.50/2.99  fof(f82,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.50/2.99    inference(definition_unfolding,[],[f48,f49])).
% 19.50/2.99  
% 19.50/2.99  fof(f23,axiom,(
% 19.50/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f64,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f23])).
% 19.50/2.99  
% 19.50/2.99  fof(f86,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.50/2.99    inference(definition_unfolding,[],[f64,f49,f75])).
% 19.50/2.99  
% 19.50/2.99  fof(f3,axiom,(
% 19.50/2.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f44,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f3])).
% 19.50/2.99  
% 19.50/2.99  fof(f76,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.50/2.99    inference(definition_unfolding,[],[f44,f49])).
% 19.50/2.99  
% 19.50/2.99  fof(f4,axiom,(
% 19.50/2.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f45,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 19.50/2.99    inference(cnf_transformation,[],[f4])).
% 19.50/2.99  
% 19.50/2.99  fof(f79,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 19.50/2.99    inference(definition_unfolding,[],[f45,f49,f51])).
% 19.50/2.99  
% 19.50/2.99  fof(f20,axiom,(
% 19.50/2.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f61,plain,(
% 19.50/2.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f20])).
% 19.50/2.99  
% 19.50/2.99  fof(f19,axiom,(
% 19.50/2.99    ! [X0] : k2_subset_1(X0) = X0),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f60,plain,(
% 19.50/2.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 19.50/2.99    inference(cnf_transformation,[],[f19])).
% 19.50/2.99  
% 19.50/2.99  fof(f24,axiom,(
% 19.50/2.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f27,plain,(
% 19.50/2.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 19.50/2.99    inference(unused_predicate_definition_removal,[],[f24])).
% 19.50/2.99  
% 19.50/2.99  fof(f34,plain,(
% 19.50/2.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 19.50/2.99    inference(ennf_transformation,[],[f27])).
% 19.50/2.99  
% 19.50/2.99  fof(f65,plain,(
% 19.50/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f34])).
% 19.50/2.99  
% 19.50/2.99  fof(f5,axiom,(
% 19.50/2.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f30,plain,(
% 19.50/2.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.50/2.99    inference(ennf_transformation,[],[f5])).
% 19.50/2.99  
% 19.50/2.99  fof(f46,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f30])).
% 19.50/2.99  
% 19.50/2.99  fof(f80,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f46,f49])).
% 19.50/2.99  
% 19.50/2.99  fof(f25,conjecture,(
% 19.50/2.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f26,negated_conjecture,(
% 19.50/2.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 19.50/2.99    inference(negated_conjecture,[],[f25])).
% 19.50/2.99  
% 19.50/2.99  fof(f28,plain,(
% 19.50/2.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 19.50/2.99    inference(pure_predicate_removal,[],[f26])).
% 19.50/2.99  
% 19.50/2.99  fof(f35,plain,(
% 19.50/2.99    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 19.50/2.99    inference(ennf_transformation,[],[f28])).
% 19.50/2.99  
% 19.50/2.99  fof(f36,plain,(
% 19.50/2.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 19.50/2.99    inference(flattening,[],[f35])).
% 19.50/2.99  
% 19.50/2.99  fof(f39,plain,(
% 19.50/2.99    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.50/2.99    introduced(choice_axiom,[])).
% 19.50/2.99  
% 19.50/2.99  fof(f38,plain,(
% 19.50/2.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 19.50/2.99    introduced(choice_axiom,[])).
% 19.50/2.99  
% 19.50/2.99  fof(f40,plain,(
% 19.50/2.99    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.50/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38])).
% 19.50/2.99  
% 19.50/2.99  fof(f69,plain,(
% 19.50/2.99    r1_xboole_0(sK1,sK2)),
% 19.50/2.99    inference(cnf_transformation,[],[f40])).
% 19.50/2.99  
% 19.50/2.99  fof(f1,axiom,(
% 19.50/2.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f37,plain,(
% 19.50/2.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 19.50/2.99    inference(nnf_transformation,[],[f1])).
% 19.50/2.99  
% 19.50/2.99  fof(f41,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f37])).
% 19.50/2.99  
% 19.50/2.99  fof(f78,plain,(
% 19.50/2.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 19.50/2.99    inference(definition_unfolding,[],[f41,f49])).
% 19.50/2.99  
% 19.50/2.99  fof(f9,axiom,(
% 19.50/2.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f50,plain,(
% 19.50/2.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.50/2.99    inference(cnf_transformation,[],[f9])).
% 19.50/2.99  
% 19.50/2.99  fof(f2,axiom,(
% 19.50/2.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f29,plain,(
% 19.50/2.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 19.50/2.99    inference(ennf_transformation,[],[f2])).
% 19.50/2.99  
% 19.50/2.99  fof(f43,plain,(
% 19.50/2.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 19.50/2.99    inference(cnf_transformation,[],[f29])).
% 19.50/2.99  
% 19.50/2.99  fof(f66,plain,(
% 19.50/2.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.50/2.99    inference(cnf_transformation,[],[f40])).
% 19.50/2.99  
% 19.50/2.99  fof(f67,plain,(
% 19.50/2.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.50/2.99    inference(cnf_transformation,[],[f40])).
% 19.50/2.99  
% 19.50/2.99  fof(f21,axiom,(
% 19.50/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f31,plain,(
% 19.50/2.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.50/2.99    inference(ennf_transformation,[],[f21])).
% 19.50/2.99  
% 19.50/2.99  fof(f32,plain,(
% 19.50/2.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.50/2.99    inference(flattening,[],[f31])).
% 19.50/2.99  
% 19.50/2.99  fof(f62,plain,(
% 19.50/2.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f32])).
% 19.50/2.99  
% 19.50/2.99  fof(f85,plain,(
% 19.50/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.50/2.99    inference(definition_unfolding,[],[f62,f51])).
% 19.50/2.99  
% 19.50/2.99  fof(f68,plain,(
% 19.50/2.99    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 19.50/2.99    inference(cnf_transformation,[],[f40])).
% 19.50/2.99  
% 19.50/2.99  fof(f42,plain,(
% 19.50/2.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.50/2.99    inference(cnf_transformation,[],[f37])).
% 19.50/2.99  
% 19.50/2.99  fof(f77,plain,(
% 19.50/2.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.50/2.99    inference(definition_unfolding,[],[f42,f49])).
% 19.50/2.99  
% 19.50/2.99  fof(f22,axiom,(
% 19.50/2.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 19.50/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.50/2.99  
% 19.50/2.99  fof(f33,plain,(
% 19.50/2.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.50/2.99    inference(ennf_transformation,[],[f22])).
% 19.50/2.99  
% 19.50/2.99  fof(f63,plain,(
% 19.50/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.50/2.99    inference(cnf_transformation,[],[f33])).
% 19.50/2.99  
% 19.50/2.99  fof(f70,plain,(
% 19.50/2.99    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 19.50/2.99    inference(cnf_transformation,[],[f40])).
% 19.50/2.99  
% 19.50/2.99  cnf(c_161,plain,( X0_2 = X0_2 ),theory(equality) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_9,plain,
% 19.50/2.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 19.50/2.99      inference(cnf_transformation,[],[f83]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(cnf_transformation,[],[f84]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1283,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_10]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5803,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1283,c_10]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_6,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(cnf_transformation,[],[f81]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5805,plain,
% 19.50/2.99      ( k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1283,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5806,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_5805,c_10]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(cnf_transformation,[],[f82]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5798,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_7,c_1283]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_15,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(cnf_transformation,[],[f86]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1282,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_0,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3122,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3125,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_3122,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3465,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_3125]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
% 19.50/2.99      inference(cnf_transformation,[],[f79]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_894,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1824,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,X0))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_894,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1830,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_1824,c_894]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_897,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_894,c_4]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1831,plain,
% 19.50/2.99      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_1830,c_897]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3121,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3126,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_3121,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3481,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_3465,c_15,c_1831,c_3126]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4309,plain,
% 19.50/2.99      ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_3481]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3564,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_7,c_3126]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4363,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_4309,c_15,c_3564]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_902,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_9983,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_4363,c_902]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4301,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_3481]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4371,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_4301,c_3481]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4372,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_4371,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5804,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1283,c_4372]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5807,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5804,c_10]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_9985,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5807,c_902]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11030,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_9985,c_5807]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3114,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7361,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_3114]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12,plain,
% 19.50/2.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 19.50/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_613,plain,
% 19.50/2.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11,plain,
% 19.50/2.99      ( k2_subset_1(X0) = X0 ),
% 19.50/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_617,plain,
% 19.50/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_613,c_11]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_16,plain,
% 19.50/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.50/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5,plain,
% 19.50/2.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.50/2.99      inference(cnf_transformation,[],[f80]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_186,plain,
% 19.50/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.50/2.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 19.50/2.99      inference(resolution,[status(thm)],[c_16,c_5]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_607,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 19.50/2.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_852,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_617,c_607]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1834,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_1831,c_894]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7365,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_7361,c_852,c_1834]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7532,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5807,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7541,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1)) = k5_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_7532,c_7365]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5023,plain,
% 19.50/2.99      ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_4363]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5089,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_5023,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10005,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_902,c_5089]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_9943,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1283,c_902]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7363,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7364,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_7363,c_1834]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10133,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_9943,c_10,c_7364]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10029,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_902,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10244,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10133,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10255,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10244,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10345,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10029,c_10133,c_10255]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10346,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10345,c_7364]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10018,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_902,c_902]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10022,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_902,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10354,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10022,c_10133,c_10255,c_10346]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10358,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(demodulation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_10018,c_10133,c_10255,c_10346,c_10354]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10359,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10358,c_7364]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_998,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10015,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_902,c_998]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10362,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10015,c_10133,c_10346,c_10354]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5489,plain,
% 19.50/2.99      ( k4_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_5089]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5594,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_5489,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10023,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_902,c_5594]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10353,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10023,c_10133,c_10346]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10363,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10362,c_10353]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10366,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10363,c_10346]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10378,plain,
% 19.50/2.99      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
% 19.50/2.99      inference(demodulation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_10005,c_10133,c_10346,c_10359,c_10362,c_10366]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10379,plain,
% 19.50/2.99      ( k4_xboole_0(X0,X0) = sP1_iProver_split ),
% 19.50/2.99      inference(splitting,
% 19.50/2.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 19.50/2.99                [c_10378]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11031,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1)) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11030,c_7365,c_7541,c_10379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10211,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5807,c_10133]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10889,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10211,c_3481]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10890,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10889,c_7541]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11032,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11031,c_10890]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10209,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_4363,c_10133]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10892,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10209,c_3564]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11036,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1))) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11032,c_10892]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11064,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,sP1_iProver_split)) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11036,c_11032]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11069,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k5_xboole_0(X0,sP1_iProver_split)) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_9983,c_11032,c_11064]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11070,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),k5_xboole_0(X0,sP1_iProver_split)) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_11069,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_999,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)),X0) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_18,negated_conjecture,
% 19.50/2.99      ( r1_xboole_0(sK1,sK2) ),
% 19.50/2.99      inference(cnf_transformation,[],[f69]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_610,plain,
% 19.50/2.99      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2,plain,
% 19.50/2.99      ( ~ r1_xboole_0(X0,X1)
% 19.50/2.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.50/2.99      inference(cnf_transformation,[],[f78]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_615,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 19.50/2.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2313,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_610,c_615]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2607,plain,
% 19.50/2.99      ( k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2313,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.50/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2610,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2607,c_8]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5883,plain,
% 19.50/2.99      ( k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2610,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3,plain,
% 19.50/2.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.50/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_614,plain,
% 19.50/2.99      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1707,plain,
% 19.50/2.99      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_610,c_614]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2314,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1707,c_615]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2744,plain,
% 19.50/2.99      ( k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2314,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2747,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2744,c_8]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_21,negated_conjecture,
% 19.50/2.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.50/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_608,plain,
% 19.50/2.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_20,negated_conjecture,
% 19.50/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.50/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_609,plain,
% 19.50/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13,plain,
% 19.50/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.50/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.50/2.99      | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
% 19.50/2.99      inference(cnf_transformation,[],[f85]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_612,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 19.50/2.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 19.50/2.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1177,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(sK2,X0)) = k4_subset_1(u1_struct_0(sK0),X0,sK2)
% 19.50/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_609,c_612]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1335,plain,
% 19.50/2.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_608,c_1177]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19,negated_conjecture,
% 19.50/2.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1338,plain,
% 19.50/2.99      ( k5_xboole_0(sK1,k4_xboole_0(sK2,sK1)) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_1335,c_19]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2976,plain,
% 19.50/2.99      ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2747,c_1338]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5907,plain,
% 19.50/2.99      ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_5883,c_2747,c_2976]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1340,plain,
% 19.50/2.99      ( k4_xboole_0(k2_struct_0(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1338,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1487,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)),k2_struct_0(sK0)) = k4_xboole_0(sK2,k2_struct_0(sK0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1340,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2752,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(sK2,sK1),k2_struct_0(sK0)) = k4_xboole_0(sK2,k2_struct_0(sK0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2610,c_1487]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5956,plain,
% 19.50/2.99      ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(sK2,k2_struct_0(sK0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5907,c_2752]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1822,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,sK2) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1340,c_894]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_850,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,u1_struct_0(sK0))) = sK2 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_609,c_607]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1007,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k4_xboole_0(sK2,sK2) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_850,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1103,plain,
% 19.50/2.99      ( k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,u1_struct_0(sK0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1007,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1105,plain,
% 19.50/2.99      ( k5_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,sK2) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_1103,c_1007]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1008,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,sK2) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_850,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1011,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) = sK2 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_1008,c_850]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1043,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1011,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1047,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_1043,c_1011]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1106,plain,
% 19.50/2.99      ( k5_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_1105,c_1047]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1862,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,sK2) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_1822,c_1106]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2748,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2747,c_2314]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3822,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 19.50/2.99      inference(light_normalisation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_1862,c_1862,c_2610,c_2748]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5957,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5907,c_3822]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5959,plain,
% 19.50/2.99      ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5956,c_5957]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_9971,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))),k5_xboole_0(k2_struct_0(sK0),k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5959,c_902]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11089,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k2_struct_0(sK0),k1_xboole_0),k5_xboole_0(k2_struct_0(sK0),k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k1_xboole_0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_9971,c_5959]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11090,plain,
% 19.50/2.99      ( sP1_iProver_split = k1_xboole_0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11089,c_8,c_5959,c_10379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11358,plain,
% 19.50/2.99      ( k5_xboole_0(X0,sP1_iProver_split) = X0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11090,c_8]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12899,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_11070,c_999,c_11070,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5882,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5910,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5882,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12956,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12899,c_5910]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12964,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12899,c_1282]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5066,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_4363,c_3114]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5070,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_5066,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5067,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_4363,c_1282]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5071,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5070,c_5067]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12967,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_12964,c_5071]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12981,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,sP1_iProver_split) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_12956,c_12899,c_12967]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12982,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_12981,c_7,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13064,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_7,c_12982]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17603,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_5798,c_13064]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17629,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17670,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17629,c_7365]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_78202,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5803,c_17670]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_83292,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_78202]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12909,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_12899]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13658,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5807,c_12909]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13894,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),sP1_iProver_split),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_13658,c_11032]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10238,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10133,c_998]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_893,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_905,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_893,c_894,c_897]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10402,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10379,c_10133]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10851,plain,
% 19.50/2.99      ( k4_xboole_0(X0,sP1_iProver_split) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10238,c_905,c_10402]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13085,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_12982]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13124,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_13085,c_7365]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13895,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_13894,c_6,c_7365,c_10851,c_11032,c_13124]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3113,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_1282]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13709,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),sP1_iProver_split)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12909,c_12982]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13739,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12909,c_3114]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_996,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1001,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_996,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13742,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_13739,c_1001]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13782,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_13709,c_13742]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10010,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_902,c_3481]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10179,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_10133]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_901,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_903,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_901,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10654,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_903]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10799,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10654,c_1834,c_10379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10800,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10799,c_998,c_10379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10852,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10851,c_10800]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10930,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10179,c_10852]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10963,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10015,c_10851,c_10930]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10964,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10963,c_10402]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10226,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10133,c_5807]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10863,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) = k4_xboole_0(sP1_iProver_split,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10226,c_10379,c_10402]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10967,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(sP1_iProver_split,X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10964,c_10863]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10981,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(sP1_iProver_split,X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10010,c_10930,c_10967]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10982,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,X0) = k4_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10981,c_10402]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10983,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,X0) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10982,c_10379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10224,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10133,c_5910]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10866,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1))) = k5_xboole_0(X1,k4_xboole_0(sP1_iProver_split,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10224,c_10379,c_10402]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10867,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,k4_xboole_0(sP1_iProver_split,X1)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10866,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10993,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,sP1_iProver_split) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10983,c_10867]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13783,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = k5_xboole_0(X1,sP1_iProver_split) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_13782,c_10993]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13784,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_13783,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17345,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_3113,c_15,c_13784]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17356,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5910,c_17345]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3123,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))),X0) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3124,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_3123,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13088,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3124,c_12982]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7776,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3124,c_1282]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7778,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_7776,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13120,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_13088,c_7778,c_11032]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10190,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(X0,X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_10133]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10913,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10190,c_10379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10914,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10913,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12717,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))),X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10914,c_5910]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12774,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0))) = k5_xboole_0(X0,k4_xboole_0(sP1_iProver_split,X0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_12717,c_10914]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12775,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = X0 ),
% 19.50/2.99      inference(light_normalisation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_12774,c_3124,c_7778,c_10983,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12776,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,X0) = X0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_12775,c_10851,c_10914]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13121,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_13120,c_10851,c_10914,c_12776]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17449,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17356,c_13121]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64107,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_17449]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68824,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_64107]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68922,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_68824,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_70541,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13895,c_68922]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_70744,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_70541,c_7365,c_10964]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_81929,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3126,c_70744]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13079,plain,
% 19.50/2.99      ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k4_xboole_0(X1,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X1 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_12982]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13127,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_13079,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13128,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_13127,c_3126]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_81978,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_81929,c_13128]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_82011,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3114,c_81978]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_34236,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3126,c_13121]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10707,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5089,c_903]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10733,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10707,c_998,c_3126]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11039,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),sP1_iProver_split)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11032,c_10733]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11056,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11039,c_10851]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11057,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11056,c_10379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_34379,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_34236,c_11057]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_75675,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10930,c_34379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17360,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_17345]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_21841,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_17360,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_21842,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_21841,c_10930]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_76357,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_75675,c_10930,c_21842]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_23846,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13784,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_23944,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_23846,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24213,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_23944]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_80855,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(sP1_iProver_split,k5_xboole_0(sP1_iProver_split,k5_xboole_0(X1,k4_xboole_0(X0,X1)))))) = k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_76357,c_24213]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10006,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_902,c_4372]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11001,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10006,c_10930,c_10964,c_10983]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5135,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_4372]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11002,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_11001,c_5135,c_10402]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_80918,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(sP1_iProver_split,k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0)))))) = k5_xboole_0(sP1_iProver_split,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_80855,c_11002,c_21842]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12947,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12899,c_3481]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12990,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_12947,c_12899]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1284,plain,
% 19.50/2.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8,c_897]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11357,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11090,c_1284]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12991,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_12990,c_11357]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_23427,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12991,c_1283]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_23534,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_23427,c_10,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24180,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,sP1_iProver_split))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10914,c_23534]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24209,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,X0)) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_24180,c_10851,c_10914]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_80919,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(sP1_iProver_split,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_80918,c_12776,c_24209]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17386,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13895,c_17345]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17419,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_17386,c_15,c_10964]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17420,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17419,c_13895]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_31389,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3114,c_17420]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7353,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_998]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7377,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = X0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_7353,c_5806,c_7365]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_32624,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3126,c_7377]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_32667,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_32624,c_13128]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_74245,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(sP1_iProver_split,k4_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_31389,c_32667]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3589,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3126,c_3125]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13102,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12982,c_4372]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13113,plain,
% 19.50/2.99      ( k4_xboole_0(sP1_iProver_split,k4_xboole_0(X0,X1)) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_13102,c_10983,c_11032]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_75134,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_74245,c_3589,c_13113]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64481,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_17449]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64553,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_64481,c_15,c_5806]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_69412,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_31389,c_64553]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13075,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12899,c_12982]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13130,plain,
% 19.50/2.99      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_13075,c_12967]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_69420,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_69412,c_13130]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17387,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),sP1_iProver_split))) = X0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10914,c_17345]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12735,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10914,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12746,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),sP1_iProver_split) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_12735,c_3124]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12747,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),sP1_iProver_split) = X0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_12746,c_11032,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17418,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17387,c_12747]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_69421,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_69420,c_12967,c_17418]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2754,plain,
% 19.50/2.99      ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2610,c_1340]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3422,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0))) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2754,c_3114]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_6082,plain,
% 19.50/2.99      ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5957,c_3422]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2743,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2314,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2758,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_2743,c_2747]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_6083,plain,
% 19.50/2.99      ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_6082,c_2758]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68827,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6083,c_64107]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68919,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = sK2 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_68827,c_6083]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68832,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13784,c_64107]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68915,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = X1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_68832,c_13784]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68842,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2754,c_64107]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68907,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_68842,c_2754]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68846,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_64107]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68904,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,X0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_68846,c_5806]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2862,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,u1_struct_0(sK0)) = k1_xboole_0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2748,c_1007]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11347,plain,
% 19.50/2.99      ( k4_xboole_0(sK2,u1_struct_0(sK0)) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11090,c_2862]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1838,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_998]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1855,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_1838,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_14843,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_1855,c_1855,c_13784]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_14858,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split),k4_xboole_0(u1_struct_0(sK0),sK2)) = sK2 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_11347,c_14843]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_15001,plain,
% 19.50/2.99      ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = sK2 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_14858,c_998,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68852,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_15001,c_64107]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68899,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = sK2 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_68852,c_15001]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2611,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2610,c_2313]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_851,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) = sK1 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_608,c_607]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1038,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k4_xboole_0(sK1,sK1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_851,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2616,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_2611,c_1038]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8282,plain,
% 19.50/2.99      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(sK1,k1_xboole_0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2616,c_5910]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2606,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2313,c_7]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2622,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_2606,c_2610]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8392,plain,
% 19.50/2.99      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_8282,c_2622]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8763,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8392,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7536,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5807,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7537,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1)),k4_xboole_0(X1,X0)) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_7536,c_7365]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7543,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_7541,c_7537]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8765,plain,
% 19.50/2.99      ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_8763,c_7543]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68853,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8765,c_64107]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68898,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = sK1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_68853,c_8765]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68877,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_31389,c_64107]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64512,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_31389,c_17449]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64521,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_64512,c_15,c_12967]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_68884,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_68877,c_12967,c_64521]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64487,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_15001,c_17449]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64548,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = sK2 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_64487,c_15001]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64488,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8765,c_17449]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64547,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = sK1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_64488,c_8765]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64475,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_17449]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_64559,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_64475,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_30195,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split))) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_11002,c_17345]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_30302,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_30195,c_10964]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_61181,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_30302]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_61218,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,X0)) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_61181,c_11057,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_62349,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sP1_iProver_split)) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_61218]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17613,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17679,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17613,c_13784]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_37293,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13784,c_17679]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13070,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_12982]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_37397,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_37293,c_13070,c_13124]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_55584,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5803,c_37397]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_55109,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_37397]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17619,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12899,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17676,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17619,c_12967]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_54997,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_17676]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5542,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5089,c_1282]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5547,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_5542,c_5071]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5753,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_1282]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5521,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5089,c_3114]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3119,plain,
% 19.50/2.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3128,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_3119,c_15,c_998]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5564,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5521,c_3128]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5522,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5089,c_1282]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5567,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5564,c_5522]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5757,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_5753,c_5567]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_55045,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_54997,c_5547,c_5757]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13105,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X1))) = X0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12982,c_1283]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_33725,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_13105]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_54336,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5803,c_33725]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24553,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1283,c_23944]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24789,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_24553,c_10]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_27774,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13784,c_24789]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_14698,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5803,c_13895]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_27889,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_27774,c_10964,c_13124,c_14698]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_53071,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_27889]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7355,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_7375,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_7355,c_5806,c_7365]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_50179,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1))),sP1_iProver_split) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_31389,c_7375]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_50655,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_50179,c_13130]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24650,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)),sP1_iProver_split)) = k5_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_12991,c_23944]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24658,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_24650,c_12967,c_13130]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_47687,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),sP1_iProver_split)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_24658]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_47732,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_47687,c_5547,c_5757]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24175,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_23534]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24811,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_24175,c_5547,c_5757]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_42808,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_24811]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_43163,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_42808,c_3128,c_11057]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_42469,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10930,c_3114]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_42473,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_42469,c_10930]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12931,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_12899]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13009,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_12931,c_5757]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_21736,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1283,c_17360]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_21989,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_21736,c_10]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_23047,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split))) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13895,c_21989]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_23085,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_23047,c_7365,c_10964,c_21989]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_39040,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13009,c_23085]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_39148,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k5_xboole_0(sP1_iProver_split,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_39040,c_13009]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_39094,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13009,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_39111,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_39094,c_13009]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_39098,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13009,c_3114]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_39103,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_39098,c_13009]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25306,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_24213]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25358,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
% 19.50/2.99      inference(light_normalisation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_25306,c_3126,c_11057,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25359,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X0)) = X0 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_25358,c_10,c_11057,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25761,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_25359]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_35524,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5803,c_25761]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_34552,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_13128]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_34593,plain,
% 19.50/2.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sP1_iProver_split) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_34552,c_3128,c_11057]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10247,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10133,c_3125]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10832,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_10247,c_6]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_10833,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_10832,c_852]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_32702,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13784,c_10833]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_32781,plain,
% 19.50/2.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = sP1_iProver_split ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_32702,c_13124,c_14698]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_29826,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5803,c_10402]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_31805,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_29826,c_1283]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_31902,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_31805,c_10964]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_1,plain,
% 19.50/2.99      ( r1_xboole_0(X0,X1)
% 19.50/2.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 19.50/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_616,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 19.50/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3120,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_616]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3127,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_3120,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11343,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11090,c_3127]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19917,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3126,c_11343]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_28905,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_19917]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_29024,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_28905,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2945,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6,c_616]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13248,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_2945,c_11090]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13313,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3126,c_13248]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_13337,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_13313,c_11057,c_11358]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_28778,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_13337]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_28897,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_28778,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25755,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) = X1 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_25359]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25794,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_25755,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_27264,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3126,c_25794]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25768,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_15001,c_25359]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25285,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(X0,X1),X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13784,c_24213]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25390,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_25285,c_13070,c_13124,c_14698]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_25268,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5803,c_24213]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24568,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_13784,c_23944]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_24771,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,
% 19.50/2.99                [status(thm)],
% 19.50/2.99                [c_24568,c_13070,c_13124,c_14698]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_21414,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_17360]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_2944,plain,
% 19.50/2.99      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(X0,k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_7,c_616]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3115,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_2944]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_3133,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_3115,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11315,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11090,c_3133]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_20665,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_7,c_11315]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_20761,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_20665,c_5564]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4397,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_3127]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4418,plain,
% 19.50/2.99      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_4397,c_15,c_3126]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4844,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_1282,c_4418]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_4881,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_4844,c_15]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11314,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) = iProver_top ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11090,c_4881]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_20535,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_7,c_11314]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_20631,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_20535,c_5564]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_20555,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3126,c_11314]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_20607,plain,
% 19.50/2.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_20555,c_5547]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19912,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_11343]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19949,plain,
% 19.50/2.99      ( sP1_iProver_split != X0
% 19.50/2.99      | r1_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_19912,c_7365]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11340,plain,
% 19.50/2.99      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11090,c_4418]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19812,plain,
% 19.50/2.99      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5806,c_11340]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19868,plain,
% 19.50/2.99      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/2.99      | r1_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_19812,c_5806]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19257,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = u1_struct_0(sK0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_15001,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5878,plain,
% 19.50/2.99      ( k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2862,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_5913,plain,
% 19.50/2.99      ( k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) = u1_struct_0(sK0) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_5878,c_8]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_14702,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) = sP1_iProver_split ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5913,c_13895]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19015,plain,
% 19.50/2.99      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sP1_iProver_split)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_14702,c_3125]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19016,plain,
% 19.50/2.99      ( k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sP1_iProver_split) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_14702,c_3114]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19020,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sP1_iProver_split) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_19016,c_15001]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19021,plain,
% 19.50/2.99      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_19015,c_19020]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_19022,plain,
% 19.50/2.99      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = sK2 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_19021,c_15001]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_18689,plain,
% 19.50/2.99      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8765,c_0]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_18732,plain,
% 19.50/2.99      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = sK1 ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_18689,c_8765]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_18690,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8765,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17625,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2754,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17673,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17625,c_6083]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_18081,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_17673]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17616,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2))) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_6083,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17678,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17616,c_2754]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17860,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_9,c_17678]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17618,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,X0))) = X0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_897,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17677,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sP1_iProver_split)) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17618,c_10379]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17637,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_5594,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17663,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17637,c_5757]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17640,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X0,sP1_iProver_split))) = X0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_10914,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17661,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17640,c_10851]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17609,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X0 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_3114,c_17603]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17371,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK1,sK2))) = sK2 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2747,c_17345]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17437,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) = sK2 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17371,c_2976]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17373,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK2,sK1))) = sK1 ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_2610,c_17345]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17435,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) = sK1 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17373,c_5907]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17385,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0)))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_4372,c_17345]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_17421,plain,
% 19.50/2.99      ( k1_setfam_1(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,X1) ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_17385,c_10964,c_11032]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8762,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8392,c_4372]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8766,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_8762,c_8765]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8767,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k1_xboole_0 ),
% 19.50/2.99      inference(light_normalisation,[status(thm)],[c_8766,c_2616]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8773,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k1_xboole_0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8767,c_1283]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8816,plain,
% 19.50/2.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_8773,c_8,c_10]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11348,plain,
% 19.50/2.99      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = sP1_iProver_split ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_11090,c_2616]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12521,plain,
% 19.50/2.99      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(sK1,sP1_iProver_split)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_11348,c_5910]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_12525,plain,
% 19.50/2.99      ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_11348,c_4372]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_9949,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)))) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8392,c_902]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_11145,plain,
% 19.50/2.99      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split)) ),
% 19.50/2.99      inference(demodulation,[status(thm)],[c_9949,c_11032]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8787,plain,
% 19.50/2.99      ( k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),sK1)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k1_xboole_0) ),
% 19.50/2.99      inference(superposition,[status(thm)],[c_8767,c_5803]) ).
% 19.50/2.99  
% 19.50/2.99  cnf(c_8796,plain,
% 19.50/2.99      ( k5_xboole_0(sK1,k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),sK1)) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_8787,c_8]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_9015,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_8796,c_6]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_7715,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(sK1,k1_xboole_0)),u1_struct_0(sK0)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2616,c_3124]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_7836,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),u1_struct_0(sK0)) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_7715,c_2622]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_8681,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_7836,c_6]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_8682,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_8681,c_8392]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_9016,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k1_xboole_0 ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_9015,c_8682,c_8767]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11146,plain,
% 19.50/3.00      ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split)) = k1_xboole_0 ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_11145,c_8765,c_9016]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_12532,plain,
% 19.50/3.00      ( k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = sP1_iProver_split ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_12525,c_11090,c_11146]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_12538,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(sK1,sP1_iProver_split)) = k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_12521,c_12532]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11354,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,sP1_iProver_split) = sK1 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_2622]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_12539,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) = k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_12538,c_11354]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_12540,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) = u1_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_12539,c_11358]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_16489,plain,
% 19.50/3.00      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_8816,c_8816,c_12540]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_8281,plain,
% 19.50/3.00      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(sK2,k1_xboole_0)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2862,c_5910]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_8393,plain,
% 19.50/3.00      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))) = k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_8281,c_2758]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_16307,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) = k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_8393,c_8393,c_14702]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_16308,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) = u1_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_16307,c_11358,c_13124]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4391,plain,
% 19.50/3.00      ( k4_xboole_0(sK2,k1_xboole_0) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(u1_struct_0(sK0),sK2) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2862,c_3127]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4422,plain,
% 19.50/3.00      ( sK2 != k1_xboole_0 | r1_xboole_0(u1_struct_0(sK0),sK2) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_4391,c_2758]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_15726,plain,
% 19.50/3.00      ( sP1_iProver_split != sK2
% 19.50/3.00      | r1_xboole_0(u1_struct_0(sK0),sK2) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_4422,c_11090]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3351,plain,
% 19.50/3.00      ( k4_xboole_0(sK2,k1_xboole_0) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(sK2,u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2862,c_616]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3362,plain,
% 19.50/3.00      ( sK2 != k1_xboole_0 | r1_xboole_0(sK2,u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_3351,c_2758]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_15722,plain,
% 19.50/3.00      ( sP1_iProver_split != sK2
% 19.50/3.00      | r1_xboole_0(sK2,u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_3362,c_11090]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1844,plain,
% 19.50/3.00      ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)) = k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK1,sK2)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_1340,c_998]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1850,plain,
% 19.50/3.00      ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK1,sK2)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1844,c_1340]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_2749,plain,
% 19.50/3.00      ( k5_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_2610,c_1850]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_14413,plain,
% 19.50/3.00      ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_6083,c_2749]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13288,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X1)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,X0)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_5807,c_13248]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13372,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_13288,c_7365,c_7541]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13373,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(demodulation,
% 19.50/3.00                [status(thm)],
% 19.50/3.00                [c_13372,c_5806,c_5807,c_7541,c_13124]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13374,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_13373,c_13124]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13309,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),k4_xboole_0(X1,X0)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),X0) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_5806,c_13248]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13343,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)),k4_xboole_0(X1,X0)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)),X0) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_13309,c_1834]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13344,plain,
% 19.50/3.00      ( sP1_iProver_split != X0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_13343,c_7365,c_10379,c_10964]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13315,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_3481,c_13248]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10705,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_3481,c_903]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10735,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10705,c_3481]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10736,plain,
% 19.50/3.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10735,c_998]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11048,plain,
% 19.50/3.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split),sP1_iProver_split)) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11032,c_10736]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11052,plain,
% 19.50/3.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split)) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11048,c_10851]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11053,plain,
% 19.50/3.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11052,c_10851]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13335,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split),sP1_iProver_split) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split),k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_13315,c_11032,c_11053]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13336,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_13335,c_10851,c_11358]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13318,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),X0)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_5807,c_13248]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13330,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),sP1_iProver_split) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_13318,c_11032]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13331,plain,
% 19.50/3.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_13330,c_7365,c_10851,c_13124]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13319,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0)),sP1_iProver_split) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10914,c_13248]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_12730,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0),k4_xboole_0(X0,sP1_iProver_split))) = sP1_iProver_split ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10914,c_10914]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_12754,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X0)) = sP1_iProver_split ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_12730,c_3124,c_10851]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_12755,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k5_xboole_0(sP1_iProver_split,X0)) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_12754,c_11032]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_12777,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),X0) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_12776,c_12755]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13329,plain,
% 19.50/3.00      ( sP1_iProver_split != X0 | r1_xboole_0(X0,X0) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,
% 19.50/3.00                [status(thm)],
% 19.50/3.00                [c_13319,c_10851,c_11358,c_12777,c_13121]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13320,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1))),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1))),u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_7836,c_13248]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_8786,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k1_xboole_0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k4_xboole_0(sK1,k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_8767,c_5806]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_8797,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1),k1_xboole_0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k1_xboole_0 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_8786,c_8767]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_8798,plain,
% 19.50/3.00      ( k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = k1_xboole_0 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_8797,c_8,c_8682]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11319,plain,
% 19.50/3.00      ( k4_xboole_0(u1_struct_0(sK0),k5_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_8798]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13327,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split),sP1_iProver_split) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(u1_struct_0(sK0),sP1_iProver_split),u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,
% 19.50/3.00                [status(thm)],
% 19.50/3.00                [c_13320,c_11319,c_12532,c_12540]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13328,plain,
% 19.50/3.00      ( u1_struct_0(sK0) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_13327,c_10851,c_11358]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6088,plain,
% 19.50/3.00      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(k2_struct_0(sK0),sK2))) = k4_xboole_0(k4_xboole_0(sK2,k2_struct_0(sK0)),sK2) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_5957,c_4372]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6122,plain,
% 19.50/3.00      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(k2_struct_0(sK0),sK2))) = k4_xboole_0(k1_xboole_0,sK2) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_6088,c_5957]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4324,plain,
% 19.50/3.00      ( k4_xboole_0(k4_xboole_0(sK2,k5_xboole_0(sK2,sK1)),sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_3822,c_3481]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4346,plain,
% 19.50/3.00      ( k4_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_4324,c_1284,c_3822]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6123,plain,
% 19.50/3.00      ( k4_xboole_0(k1_xboole_0,k2_struct_0(sK0)) = k1_xboole_0 ),
% 19.50/3.00      inference(light_normalisation,
% 19.50/3.00                [status(thm)],
% 19.50/3.00                [c_6122,c_2754,c_4346,c_5907]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11335,plain,
% 19.50/3.00      ( k4_xboole_0(sP1_iProver_split,k2_struct_0(sK0)) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_6123]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13321,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(sP1_iProver_split,k4_xboole_0(k2_struct_0(sK0),sP1_iProver_split)),sP1_iProver_split) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(sP1_iProver_split,k4_xboole_0(k2_struct_0(sK0),sP1_iProver_split)),k2_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_11335,c_13248]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6248,plain,
% 19.50/3.00      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)) = k5_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_6123,c_5803]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6251,plain,
% 19.50/3.00      ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_6123,c_3125]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6254,plain,
% 19.50/3.00      ( k5_xboole_0(k2_struct_0(sK0),k1_xboole_0) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_6251,c_1284]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6255,plain,
% 19.50/3.00      ( k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_6254,c_8]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6261,plain,
% 19.50/3.00      ( k5_xboole_0(k1_xboole_0,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k1_xboole_0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_6248,c_6255]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6262,plain,
% 19.50/3.00      ( k5_xboole_0(k1_xboole_0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_6261,c_8]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11332,plain,
% 19.50/3.00      ( k5_xboole_0(sP1_iProver_split,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_6262]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11333,plain,
% 19.50/3.00      ( k4_xboole_0(k2_struct_0(sK0),sP1_iProver_split) = k2_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_6255]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_13326,plain,
% 19.50/3.00      ( k2_struct_0(sK0) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_13321,c_11332,c_11333]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4400,plain,
% 19.50/3.00      ( k4_xboole_0(k2_struct_0(sK0),sK1) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(sK2,k2_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2754,c_3127]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11341,plain,
% 19.50/3.00      ( k4_xboole_0(k2_struct_0(sK0),sK1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(sK2,k2_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_4400]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11360,plain,
% 19.50/3.00      ( sP1_iProver_split != sK2
% 19.50/3.00      | r1_xboole_0(sK2,k2_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_11341,c_6083]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_2951,plain,
% 19.50/3.00      ( k4_xboole_0(k2_struct_0(sK0),sK1) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2754,c_616]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11342,plain,
% 19.50/3.00      ( k4_xboole_0(k2_struct_0(sK0),sK1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_2951]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11359,plain,
% 19.50/3.00      ( sP1_iProver_split != sK2
% 19.50/3.00      | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_11342,c_6083]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11356,plain,
% 19.50/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_615]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11352,plain,
% 19.50/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_616]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11351,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(X0,k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_2944]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1814,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_1338,c_894]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1169,plain,
% 19.50/3.00      ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_1038,c_0]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1171,plain,
% 19.50/3.00      ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK1,sK1) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_1169,c_1038]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1039,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_851,c_0]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1042,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = sK1 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_1039,c_851]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1097,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_1042,c_7]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1101,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK1 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_1097,c_1042]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1172,plain,
% 19.50/3.00      ( k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1171,c_1101]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1869,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(sK1,sK1) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1814,c_1172]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_2615,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_2611,c_1869]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11349,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_2615]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3045,plain,
% 19.50/3.00      ( sK1 != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2754,c_2944]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3052,plain,
% 19.50/3.00      ( sK1 != k1_xboole_0 | r1_xboole_0(k2_struct_0(sK0),sK1) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_3045,c_2754]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11345,plain,
% 19.50/3.00      ( sP1_iProver_split != sK1
% 19.50/3.00      | r1_xboole_0(k2_struct_0(sK0),sK1) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_3052]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11336,plain,
% 19.50/3.00      ( k4_xboole_0(sK2,k2_struct_0(sK0)) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_5957]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3253,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(sK1,k2_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2615,c_616]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3264,plain,
% 19.50/3.00      ( sK1 != k1_xboole_0 | r1_xboole_0(sK1,k2_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_3253,c_2622]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11328,plain,
% 19.50/3.00      ( sP1_iProver_split != sK1
% 19.50/3.00      | r1_xboole_0(sK1,k2_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_3264]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3336,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(sK1,u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2616,c_616]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3347,plain,
% 19.50/3.00      ( sK1 != k1_xboole_0 | r1_xboole_0(sK1,u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_3336,c_2622]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11325,plain,
% 19.50/3.00      ( sP1_iProver_split != sK1
% 19.50/3.00      | r1_xboole_0(sK1,u1_struct_0(sK0)) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_3347]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4392,plain,
% 19.50/3.00      ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(u1_struct_0(sK0),sK1) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2616,c_3127]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4421,plain,
% 19.50/3.00      ( sK1 != k1_xboole_0 | r1_xboole_0(u1_struct_0(sK0),sK1) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_4392,c_2622]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11324,plain,
% 19.50/3.00      ( sP1_iProver_split != sK1
% 19.50/3.00      | r1_xboole_0(u1_struct_0(sK0),sK1) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_4421]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3038,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_6,c_2944]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3059,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_3038,c_6]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11318,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_3059]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4836,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_6,c_4418]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4888,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_4836,c_6]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11313,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X1) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_4888]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_9996,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_902,c_3133]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11012,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_9996,c_10851,c_10930]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11013,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_11012,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11092,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_11013]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11111,plain,
% 19.50/3.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11092,c_10851]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10009,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_902,c_3127]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10998,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10009,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11093,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_10998]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11110,plain,
% 19.50/3.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11093,c_10851]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10014,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_902,c_616]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10978,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10014,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11094,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_10978]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11109,plain,
% 19.50/3.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11094,c_10851]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10232,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X0) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10133,c_4418]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10858,plain,
% 19.50/3.00      ( sP1_iProver_split != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(sP1_iProver_split,X0) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10232,c_10379,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11099,plain,
% 19.50/3.00      ( sP1_iProver_split != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(sP1_iProver_split,X0) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_10858]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11106,plain,
% 19.50/3.00      ( r1_xboole_0(sP1_iProver_split,X0) = iProver_top ),
% 19.50/3.00      inference(equality_resolution_simp,[status(thm)],[c_11099]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10236,plain,
% 19.50/3.00      ( k4_xboole_0(X0,X0) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10133,c_2944]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10855,plain,
% 19.50/3.00      ( sP1_iProver_split != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(X0,sP1_iProver_split) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10236,c_10379,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11101,plain,
% 19.50/3.00      ( sP1_iProver_split != sP1_iProver_split
% 19.50/3.00      | r1_xboole_0(X0,sP1_iProver_split) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_10855]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11105,plain,
% 19.50/3.00      ( r1_xboole_0(X0,sP1_iProver_split) = iProver_top ),
% 19.50/3.00      inference(equality_resolution_simp,[status(thm)],[c_11101]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10237,plain,
% 19.50/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10133,c_616]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10854,plain,
% 19.50/3.00      ( k1_xboole_0 != X0
% 19.50/3.00      | r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10237,c_852]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11102,plain,
% 19.50/3.00      ( sP1_iProver_split != X0
% 19.50/3.00      | r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_10854]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10233,plain,
% 19.50/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) != k1_xboole_0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10133,c_3127]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10857,plain,
% 19.50/3.00      ( k1_xboole_0 != X0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10233,c_852]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11100,plain,
% 19.50/3.00      ( sP1_iProver_split != X0
% 19.50/3.00      | r1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11090,c_10857]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10241,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10133,c_5910]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10845,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10241,c_6,c_4372]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10846,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10845,c_852]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11044,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_11032,c_10846]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_9998,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_902,c_5910]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11009,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.50/3.00      inference(demodulation,
% 19.50/3.00                [status(thm)],
% 19.50/3.00                [c_9998,c_10851,c_10930,c_10964,c_11002]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_11010,plain,
% 19.50/3.00      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_11009,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10019,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_902,c_5910]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10231,plain,
% 19.50/3.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),X0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10133,c_4372]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10859,plain,
% 19.50/3.00      ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),X0))) = k4_xboole_0(sP1_iProver_split,X0) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10231,c_10379,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10860,plain,
% 19.50/3.00      ( k4_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(sP1_iProver_split,X0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10859,c_6]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10955,plain,
% 19.50/3.00      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(sP1_iProver_split,X1)) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10019,c_10860,c_10930]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10956,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(sP1_iProver_split,X0)) = k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10955,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10986,plain,
% 19.50/3.00      ( k5_xboole_0(sP1_iProver_split,k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split)) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10983,c_10956]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10997,plain,
% 19.50/3.00      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10986,c_10851,c_10964]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10229,plain,
% 19.50/3.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X0)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_10133,c_1283]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10862,plain,
% 19.50/3.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10229,c_10379]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10974,plain,
% 19.50/3.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10964,c_10862]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10949,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10022,c_10930]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10950,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),sP1_iProver_split) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10949,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10028,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_902,c_3114]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10938,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10028,c_10851,c_10930]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10939,plain,
% 19.50/3.00      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10938,c_10402]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10629,plain,
% 19.50/3.00      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_998,c_903]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10827,plain,
% 19.50/3.00      ( k5_xboole_0(X0,k4_xboole_0(X0,sP1_iProver_split)) = sP1_iProver_split ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10629,c_852,c_10379]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10853,plain,
% 19.50/3.00      ( k5_xboole_0(X0,X0) = sP1_iProver_split ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10851,c_10827]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10838,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_10244,c_6]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_10839,plain,
% 19.50/3.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),sP1_iProver_split) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_10838,c_10379]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_7362,plain,
% 19.50/3.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_5806,c_1282]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_7366,plain,
% 19.50/3.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_7365,c_7362]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6101,plain,
% 19.50/3.00      ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_5957,c_3125]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_6105,plain,
% 19.50/3.00      ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_6101,c_2754,c_2758]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1178,plain,
% 19.50/3.00      ( k5_xboole_0(X0,k4_xboole_0(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),X0,sK1)
% 19.50/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_608,c_612]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1491,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_609,c_1178]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_2753,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,sK1) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_2610,c_1491]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5958,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_5907,c_2753]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1179,plain,
% 19.50/3.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X1,X0,X1)
% 19.50/3.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_617,c_612]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5457,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_608,c_1179]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5879,plain,
% 19.50/3.00      ( k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2616,c_5803]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5912,plain,
% 19.50/3.00      ( k5_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_5879,c_8]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5955,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_5457,c_5457,c_5912]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5456,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_609,c_1179]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5918,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_5456,c_5456,c_5913]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5458,plain,
% 19.50/3.00      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_subset_1(X0,X0,X0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_617,c_1179]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_5459,plain,
% 19.50/3.00      ( k4_subset_1(X0,X0,X0) = X0 ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_5458,c_905]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1493,plain,
% 19.50/3.00      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_617,c_1178]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1494,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,sK1)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1493,c_1038]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4764,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1494,c_1494,c_2611]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4765,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_4764,c_8,c_1494]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1336,plain,
% 19.50/3.00      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_617,c_1177]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1337,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK2,sK2)) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1336,c_1007]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4710,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1337,c_1337,c_2748]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_4711,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = u1_struct_0(sK0) ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_4710,c_8,c_1337]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3459,plain,
% 19.50/3.00      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2862,c_3125]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3485,plain,
% 19.50/3.00      ( k5_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_3459,c_2758]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3460,plain,
% 19.50/3.00      ( k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,k1_xboole_0)) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_2616,c_3125]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3484,plain,
% 19.50/3.00      ( k5_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_3460,c_2622]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_14,plain,
% 19.50/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.50/3.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 19.50/3.00      inference(cnf_transformation,[],[f63]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_611,plain,
% 19.50/3.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 19.50/3.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 19.50/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3074,plain,
% 19.50/3.00      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_617,c_611]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3073,plain,
% 19.50/3.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_608,c_611]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_3072,plain,
% 19.50/3.00      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_609,c_611]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1492,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_608,c_1178]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1098,plain,
% 19.50/3.00      ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_1042,c_0]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1100,plain,
% 19.50/3.00      ( k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = sK1 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_1098,c_1042]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1495,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1492,c_1100]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1334,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_609,c_1177]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1044,plain,
% 19.50/3.00      ( k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k5_xboole_0(sK2,sK2)) ),
% 19.50/3.00      inference(superposition,[status(thm)],[c_1011,c_0]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1046,plain,
% 19.50/3.00      ( k5_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
% 19.50/3.00      inference(demodulation,[status(thm)],[c_1044,c_1011]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_1339,plain,
% 19.50/3.00      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
% 19.50/3.00      inference(light_normalisation,[status(thm)],[c_1334,c_1046]) ).
% 19.50/3.00  
% 19.50/3.00  cnf(c_17,negated_conjecture,
% 19.50/3.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 19.50/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.50/3.00  
% 19.50/3.00  
% 19.50/3.00  % SZS output end Saturation for theBenchmark.p
% 19.50/3.00  
% 19.50/3.00  ------                               Statistics
% 19.50/3.00  
% 19.50/3.00  ------ General
% 19.50/3.00  
% 19.50/3.00  abstr_ref_over_cycles:                  0
% 19.50/3.00  abstr_ref_under_cycles:                 0
% 19.50/3.00  gc_basic_clause_elim:                   0
% 19.50/3.00  forced_gc_time:                         0
% 19.50/3.00  parsing_time:                           0.009
% 19.50/3.00  unif_index_cands_time:                  0.
% 19.50/3.00  unif_index_add_time:                    0.
% 19.50/3.00  orderings_time:                         0.
% 19.50/3.00  out_proof_time:                         0.
% 19.50/3.00  total_time:                             2.331
% 19.50/3.00  num_of_symbols:                         51
% 19.50/3.00  num_of_terms:                           63432
% 19.50/3.00  
% 19.50/3.00  ------ Preprocessing
% 19.50/3.00  
% 19.50/3.00  num_of_splits:                          0
% 19.50/3.00  num_of_split_atoms:                     2
% 19.50/3.00  num_of_reused_defs:                     0
% 19.50/3.00  num_eq_ax_congr_red:                    32
% 19.50/3.00  num_of_sem_filtered_clauses:            1
% 19.50/3.00  num_of_subtypes:                        0
% 19.50/3.00  monotx_restored_types:                  0
% 19.50/3.00  sat_num_of_epr_types:                   0
% 19.50/3.00  sat_num_of_non_cyclic_types:            0
% 19.50/3.00  sat_guarded_non_collapsed_types:        0
% 19.50/3.00  num_pure_diseq_elim:                    0
% 19.50/3.00  simp_replaced_by:                       0
% 19.50/3.00  res_preprocessed:                       112
% 19.50/3.00  prep_upred:                             0
% 19.50/3.00  prep_unflattend:                        0
% 19.50/3.00  smt_new_axioms:                         0
% 19.50/3.00  pred_elim_cands:                        2
% 19.50/3.00  pred_elim:                              1
% 19.50/3.00  pred_elim_cl:                           1
% 19.50/3.00  pred_elim_cycles:                       3
% 19.50/3.00  merged_defs:                            8
% 19.50/3.00  merged_defs_ncl:                        0
% 19.50/3.00  bin_hyper_res:                          8
% 19.50/3.00  prep_cycles:                            4
% 19.50/3.00  pred_elim_time:                         0.
% 19.50/3.00  splitting_time:                         0.
% 19.50/3.00  sem_filter_time:                        0.
% 19.50/3.00  monotx_time:                            0.
% 19.50/3.00  subtype_inf_time:                       0.
% 19.50/3.00  
% 19.50/3.00  ------ Problem properties
% 19.50/3.00  
% 19.50/3.00  clauses:                                21
% 19.50/3.00  conjectures:                            5
% 19.50/3.00  epr:                                    2
% 19.50/3.00  horn:                                   21
% 19.50/3.00  ground:                                 5
% 19.50/3.00  unary:                                  15
% 19.50/3.00  binary:                                 5
% 19.50/3.00  lits:                                   28
% 19.50/3.00  lits_eq:                                16
% 19.50/3.00  fd_pure:                                0
% 19.50/3.00  fd_pseudo:                              0
% 19.50/3.00  fd_cond:                                0
% 19.50/3.00  fd_pseudo_cond:                         0
% 19.50/3.00  ac_symbols:                             0
% 19.50/3.00  
% 19.50/3.00  ------ Propositional Solver
% 19.50/3.00  
% 19.50/3.00  prop_solver_calls:                      37
% 19.50/3.00  prop_fast_solver_calls:                 1490
% 19.50/3.00  smt_solver_calls:                       0
% 19.50/3.00  smt_fast_solver_calls:                  0
% 19.50/3.00  prop_num_of_clauses:                    12862
% 19.50/3.00  prop_preprocess_simplified:             22943
% 19.50/3.00  prop_fo_subsumed:                       3
% 19.50/3.00  prop_solver_time:                       0.
% 19.50/3.00  smt_solver_time:                        0.
% 19.50/3.00  smt_fast_solver_time:                   0.
% 19.50/3.00  prop_fast_solver_time:                  0.
% 19.50/3.00  prop_unsat_core_time:                   0.
% 19.50/3.00  
% 19.50/3.00  ------ QBF
% 19.50/3.00  
% 19.50/3.00  qbf_q_res:                              0
% 19.50/3.00  qbf_num_tautologies:                    0
% 19.50/3.00  qbf_prep_cycles:                        0
% 19.50/3.00  
% 19.50/3.00  ------ BMC1
% 19.50/3.00  
% 19.50/3.00  bmc1_current_bound:                     -1
% 19.50/3.00  bmc1_last_solved_bound:                 -1
% 19.50/3.00  bmc1_unsat_core_size:                   -1
% 19.50/3.00  bmc1_unsat_core_parents_size:           -1
% 19.50/3.00  bmc1_merge_next_fun:                    0
% 19.50/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.50/3.00  
% 19.50/3.00  ------ Instantiation
% 19.50/3.00  
% 19.50/3.00  inst_num_of_clauses:                    6304
% 19.50/3.00  inst_num_in_passive:                    2750
% 19.50/3.00  inst_num_in_active:                     1723
% 19.50/3.00  inst_num_in_unprocessed:                1831
% 19.50/3.00  inst_num_of_loops:                      2030
% 19.50/3.00  inst_num_of_learning_restarts:          0
% 19.50/3.00  inst_num_moves_active_passive:          301
% 19.50/3.00  inst_lit_activity:                      0
% 19.50/3.00  inst_lit_activity_moves:                2
% 19.50/3.00  inst_num_tautologies:                   0
% 19.50/3.00  inst_num_prop_implied:                  0
% 19.50/3.00  inst_num_existing_simplified:           0
% 19.50/3.00  inst_num_eq_res_simplified:             0
% 19.50/3.00  inst_num_child_elim:                    0
% 19.50/3.00  inst_num_of_dismatching_blockings:      1582
% 19.50/3.00  inst_num_of_non_proper_insts:           5168
% 19.50/3.00  inst_num_of_duplicates:                 0
% 19.50/3.00  inst_inst_num_from_inst_to_res:         0
% 19.50/3.00  inst_dismatching_checking_time:         0.
% 19.50/3.00  
% 19.50/3.00  ------ Resolution
% 19.50/3.00  
% 19.50/3.00  res_num_of_clauses:                     0
% 19.50/3.00  res_num_in_passive:                     0
% 19.50/3.00  res_num_in_active:                      0
% 19.50/3.00  res_num_of_loops:                       116
% 19.50/3.00  res_forward_subset_subsumed:            4561
% 19.50/3.00  res_backward_subset_subsumed:           0
% 19.50/3.00  res_forward_subsumed:                   0
% 19.50/3.00  res_backward_subsumed:                  0
% 19.50/3.00  res_forward_subsumption_resolution:     0
% 19.50/3.00  res_backward_subsumption_resolution:    0
% 19.50/3.00  res_clause_to_clause_subsumption:       13109
% 19.50/3.00  res_orphan_elimination:                 0
% 19.50/3.00  res_tautology_del:                      438
% 19.50/3.00  res_num_eq_res_simplified:              0
% 19.50/3.00  res_num_sel_changes:                    0
% 19.50/3.00  res_moves_from_active_to_pass:          0
% 19.50/3.00  
% 19.50/3.00  ------ Superposition
% 19.50/3.00  
% 19.50/3.00  sup_time_total:                         0.
% 19.50/3.00  sup_time_generating:                    0.
% 19.50/3.00  sup_time_sim_full:                      0.
% 19.50/3.00  sup_time_sim_immed:                     0.
% 19.50/3.00  
% 19.50/3.00  sup_num_of_clauses:                     721
% 19.50/3.00  sup_num_in_active:                      221
% 19.50/3.00  sup_num_in_passive:                     500
% 19.50/3.00  sup_num_of_loops:                       404
% 19.50/3.00  sup_fw_superposition:                   27495
% 19.50/3.00  sup_bw_superposition:                   12021
% 19.50/3.00  sup_immediate_simplified:               14300
% 19.50/3.00  sup_given_eliminated:                   13
% 19.50/3.00  comparisons_done:                       0
% 19.50/3.00  comparisons_avoided:                    0
% 19.50/3.00  
% 19.50/3.00  ------ Simplifications
% 19.50/3.00  
% 19.50/3.00  
% 19.50/3.00  sim_fw_subset_subsumed:                 64
% 19.50/3.00  sim_bw_subset_subsumed:                 0
% 19.50/3.00  sim_fw_subsumed:                        822
% 19.50/3.00  sim_bw_subsumed:                        99
% 19.50/3.00  sim_fw_subsumption_res:                 0
% 19.50/3.00  sim_bw_subsumption_res:                 0
% 19.50/3.00  sim_tautology_del:                      0
% 19.50/3.00  sim_eq_tautology_del:                   6854
% 19.50/3.00  sim_eq_res_simp:                        388
% 19.50/3.00  sim_fw_demodulated:                     7317
% 19.50/3.00  sim_bw_demodulated:                     303
% 19.50/3.00  sim_light_normalised:                   11043
% 19.50/3.00  sim_joinable_taut:                      0
% 19.50/3.00  sim_joinable_simp:                      0
% 19.50/3.00  sim_ac_normalised:                      0
% 19.50/3.00  sim_smt_subsumption:                    0
% 19.50/3.00  
%------------------------------------------------------------------------------

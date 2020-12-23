%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:34 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 815 expanded)
%              Number of clauses        :   39 (  71 expanded)
%              Number of leaves         :   22 ( 264 expanded)
%              Depth                    :   15
%              Number of atoms          :  209 (1223 expanded)
%              Number of equality atoms :   75 ( 686 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f60])).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f38,f62,f60,f61])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f36,f62,f60,f60,f62])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f33,f60,f60,f60,f60])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(definition_unfolding,[],[f37,f61,f60,f60,f61])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f60])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,sK2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,sK2)))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(X0,sK1),k5_relat_1(X0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29,f28])).

fof(f54,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f54,f60,f60])).

fof(f51,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f60])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_395,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1205,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_395])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_745,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_398,plain,
    ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(light_normalisation,[status(thm)],[c_4,c_0])).

cnf(c_753,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_745,c_398])).

cnf(c_1207,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1205,c_753])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_67,plain,
    ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_8,c_6])).

cnf(c_68,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(renaming,[status(thm)],[c_67])).

cnf(c_390,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_396,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_394,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_805,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) != iProver_top
    | r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_396,c_394])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_512,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,X0))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_513,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,X0)) = iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_515,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) = iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_821,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_822,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_870,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_805,c_14,c_15,c_515,c_822])).

cnf(c_874,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_390,c_870])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_421,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_422,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) = iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_945,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_874,c_14,c_15,c_16,c_422,c_515,c_805,c_822])).

cnf(c_1529,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1207,c_945])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.61/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.98  
% 3.61/0.98  ------  iProver source info
% 3.61/0.98  
% 3.61/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.98  git: non_committed_changes: false
% 3.61/0.98  git: last_make_outside_of_git: false
% 3.61/0.98  
% 3.61/0.98  ------ 
% 3.61/0.98  
% 3.61/0.98  ------ Input Options
% 3.61/0.98  
% 3.61/0.98  --out_options                           all
% 3.61/0.98  --tptp_safe_out                         true
% 3.61/0.98  --problem_path                          ""
% 3.61/0.98  --include_path                          ""
% 3.61/0.98  --clausifier                            res/vclausify_rel
% 3.61/0.98  --clausifier_options                    ""
% 3.61/0.98  --stdin                                 false
% 3.61/0.98  --stats_out                             all
% 3.61/0.98  
% 3.61/0.98  ------ General Options
% 3.61/0.98  
% 3.61/0.98  --fof                                   false
% 3.61/0.98  --time_out_real                         305.
% 3.61/0.98  --time_out_virtual                      -1.
% 3.61/0.98  --symbol_type_check                     false
% 3.61/0.98  --clausify_out                          false
% 3.61/0.98  --sig_cnt_out                           false
% 3.61/0.98  --trig_cnt_out                          false
% 3.61/0.98  --trig_cnt_out_tolerance                1.
% 3.61/0.98  --trig_cnt_out_sk_spl                   false
% 3.61/0.98  --abstr_cl_out                          false
% 3.61/0.98  
% 3.61/0.98  ------ Global Options
% 3.61/0.98  
% 3.61/0.98  --schedule                              default
% 3.61/0.98  --add_important_lit                     false
% 3.61/0.98  --prop_solver_per_cl                    1000
% 3.61/0.98  --min_unsat_core                        false
% 3.61/0.98  --soft_assumptions                      false
% 3.61/0.98  --soft_lemma_size                       3
% 3.61/0.98  --prop_impl_unit_size                   0
% 3.61/0.98  --prop_impl_unit                        []
% 3.61/0.98  --share_sel_clauses                     true
% 3.61/0.98  --reset_solvers                         false
% 3.61/0.98  --bc_imp_inh                            [conj_cone]
% 3.61/0.98  --conj_cone_tolerance                   3.
% 3.61/0.98  --extra_neg_conj                        none
% 3.61/0.98  --large_theory_mode                     true
% 3.61/0.98  --prolific_symb_bound                   200
% 3.61/0.98  --lt_threshold                          2000
% 3.61/0.98  --clause_weak_htbl                      true
% 3.61/0.98  --gc_record_bc_elim                     false
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing Options
% 3.61/0.98  
% 3.61/0.98  --preprocessing_flag                    true
% 3.61/0.98  --time_out_prep_mult                    0.1
% 3.61/0.98  --splitting_mode                        input
% 3.61/0.98  --splitting_grd                         true
% 3.61/0.98  --splitting_cvd                         false
% 3.61/0.98  --splitting_cvd_svl                     false
% 3.61/0.98  --splitting_nvd                         32
% 3.61/0.98  --sub_typing                            true
% 3.61/0.98  --prep_gs_sim                           true
% 3.61/0.98  --prep_unflatten                        true
% 3.61/0.98  --prep_res_sim                          true
% 3.61/0.98  --prep_upred                            true
% 3.61/0.98  --prep_sem_filter                       exhaustive
% 3.61/0.98  --prep_sem_filter_out                   false
% 3.61/0.98  --pred_elim                             true
% 3.61/0.98  --res_sim_input                         true
% 3.61/0.98  --eq_ax_congr_red                       true
% 3.61/0.98  --pure_diseq_elim                       true
% 3.61/0.98  --brand_transform                       false
% 3.61/0.98  --non_eq_to_eq                          false
% 3.61/0.98  --prep_def_merge                        true
% 3.61/0.98  --prep_def_merge_prop_impl              false
% 3.61/0.98  --prep_def_merge_mbd                    true
% 3.61/0.98  --prep_def_merge_tr_red                 false
% 3.61/0.98  --prep_def_merge_tr_cl                  false
% 3.61/0.98  --smt_preprocessing                     true
% 3.61/0.98  --smt_ac_axioms                         fast
% 3.61/0.98  --preprocessed_out                      false
% 3.61/0.98  --preprocessed_stats                    false
% 3.61/0.98  
% 3.61/0.98  ------ Abstraction refinement Options
% 3.61/0.98  
% 3.61/0.98  --abstr_ref                             []
% 3.61/0.98  --abstr_ref_prep                        false
% 3.61/0.98  --abstr_ref_until_sat                   false
% 3.61/0.98  --abstr_ref_sig_restrict                funpre
% 3.61/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.98  --abstr_ref_under                       []
% 3.61/0.98  
% 3.61/0.98  ------ SAT Options
% 3.61/0.98  
% 3.61/0.98  --sat_mode                              false
% 3.61/0.98  --sat_fm_restart_options                ""
% 3.61/0.98  --sat_gr_def                            false
% 3.61/0.98  --sat_epr_types                         true
% 3.61/0.98  --sat_non_cyclic_types                  false
% 3.61/0.98  --sat_finite_models                     false
% 3.61/0.98  --sat_fm_lemmas                         false
% 3.61/0.98  --sat_fm_prep                           false
% 3.61/0.98  --sat_fm_uc_incr                        true
% 3.61/0.98  --sat_out_model                         small
% 3.61/0.98  --sat_out_clauses                       false
% 3.61/0.98  
% 3.61/0.98  ------ QBF Options
% 3.61/0.98  
% 3.61/0.98  --qbf_mode                              false
% 3.61/0.98  --qbf_elim_univ                         false
% 3.61/0.98  --qbf_dom_inst                          none
% 3.61/0.98  --qbf_dom_pre_inst                      false
% 3.61/0.98  --qbf_sk_in                             false
% 3.61/0.98  --qbf_pred_elim                         true
% 3.61/0.98  --qbf_split                             512
% 3.61/0.98  
% 3.61/0.98  ------ BMC1 Options
% 3.61/0.98  
% 3.61/0.98  --bmc1_incremental                      false
% 3.61/0.98  --bmc1_axioms                           reachable_all
% 3.61/0.98  --bmc1_min_bound                        0
% 3.61/0.98  --bmc1_max_bound                        -1
% 3.61/0.98  --bmc1_max_bound_default                -1
% 3.61/0.98  --bmc1_symbol_reachability              true
% 3.61/0.98  --bmc1_property_lemmas                  false
% 3.61/0.98  --bmc1_k_induction                      false
% 3.61/0.98  --bmc1_non_equiv_states                 false
% 3.61/0.98  --bmc1_deadlock                         false
% 3.61/0.98  --bmc1_ucm                              false
% 3.61/0.98  --bmc1_add_unsat_core                   none
% 3.61/0.98  --bmc1_unsat_core_children              false
% 3.61/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.98  --bmc1_out_stat                         full
% 3.61/0.98  --bmc1_ground_init                      false
% 3.61/0.98  --bmc1_pre_inst_next_state              false
% 3.61/0.98  --bmc1_pre_inst_state                   false
% 3.61/0.98  --bmc1_pre_inst_reach_state             false
% 3.61/0.98  --bmc1_out_unsat_core                   false
% 3.61/0.98  --bmc1_aig_witness_out                  false
% 3.61/0.98  --bmc1_verbose                          false
% 3.61/0.98  --bmc1_dump_clauses_tptp                false
% 3.61/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.98  --bmc1_dump_file                        -
% 3.61/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.98  --bmc1_ucm_extend_mode                  1
% 3.61/0.98  --bmc1_ucm_init_mode                    2
% 3.61/0.98  --bmc1_ucm_cone_mode                    none
% 3.61/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.98  --bmc1_ucm_relax_model                  4
% 3.61/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.98  --bmc1_ucm_layered_model                none
% 3.61/0.98  --bmc1_ucm_max_lemma_size               10
% 3.61/0.98  
% 3.61/0.98  ------ AIG Options
% 3.61/0.98  
% 3.61/0.98  --aig_mode                              false
% 3.61/0.98  
% 3.61/0.98  ------ Instantiation Options
% 3.61/0.98  
% 3.61/0.98  --instantiation_flag                    true
% 3.61/0.98  --inst_sos_flag                         true
% 3.61/0.98  --inst_sos_phase                        true
% 3.61/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.98  --inst_lit_sel_side                     num_symb
% 3.61/0.98  --inst_solver_per_active                1400
% 3.61/0.98  --inst_solver_calls_frac                1.
% 3.61/0.98  --inst_passive_queue_type               priority_queues
% 3.61/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.98  --inst_passive_queues_freq              [25;2]
% 3.61/0.98  --inst_dismatching                      true
% 3.61/0.98  --inst_eager_unprocessed_to_passive     true
% 3.61/0.98  --inst_prop_sim_given                   true
% 3.61/0.98  --inst_prop_sim_new                     false
% 3.61/0.98  --inst_subs_new                         false
% 3.61/0.98  --inst_eq_res_simp                      false
% 3.61/0.98  --inst_subs_given                       false
% 3.61/0.98  --inst_orphan_elimination               true
% 3.61/0.98  --inst_learning_loop_flag               true
% 3.61/0.98  --inst_learning_start                   3000
% 3.61/0.98  --inst_learning_factor                  2
% 3.61/0.98  --inst_start_prop_sim_after_learn       3
% 3.61/0.98  --inst_sel_renew                        solver
% 3.61/0.98  --inst_lit_activity_flag                true
% 3.61/0.98  --inst_restr_to_given                   false
% 3.61/0.98  --inst_activity_threshold               500
% 3.61/0.98  --inst_out_proof                        true
% 3.61/0.98  
% 3.61/0.98  ------ Resolution Options
% 3.61/0.98  
% 3.61/0.98  --resolution_flag                       true
% 3.61/0.98  --res_lit_sel                           adaptive
% 3.61/0.98  --res_lit_sel_side                      none
% 3.61/0.98  --res_ordering                          kbo
% 3.61/0.98  --res_to_prop_solver                    active
% 3.61/0.98  --res_prop_simpl_new                    false
% 3.61/0.98  --res_prop_simpl_given                  true
% 3.61/0.98  --res_passive_queue_type                priority_queues
% 3.61/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.98  --res_passive_queues_freq               [15;5]
% 3.61/0.98  --res_forward_subs                      full
% 3.61/0.98  --res_backward_subs                     full
% 3.61/0.98  --res_forward_subs_resolution           true
% 3.61/0.98  --res_backward_subs_resolution          true
% 3.61/0.98  --res_orphan_elimination                true
% 3.61/0.98  --res_time_limit                        2.
% 3.61/0.98  --res_out_proof                         true
% 3.61/0.98  
% 3.61/0.98  ------ Superposition Options
% 3.61/0.98  
% 3.61/0.98  --superposition_flag                    true
% 3.61/0.98  --sup_passive_queue_type                priority_queues
% 3.61/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.98  --demod_completeness_check              fast
% 3.61/0.98  --demod_use_ground                      true
% 3.61/0.98  --sup_to_prop_solver                    passive
% 3.61/0.98  --sup_prop_simpl_new                    true
% 3.61/0.98  --sup_prop_simpl_given                  true
% 3.61/0.98  --sup_fun_splitting                     true
% 3.61/0.98  --sup_smt_interval                      50000
% 3.61/0.98  
% 3.61/0.98  ------ Superposition Simplification Setup
% 3.61/0.98  
% 3.61/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.61/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.61/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.61/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.61/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.61/0.98  --sup_immed_triv                        [TrivRules]
% 3.61/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.98  --sup_immed_bw_main                     []
% 3.61/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.61/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.98  --sup_input_bw                          []
% 3.61/0.98  
% 3.61/0.98  ------ Combination Options
% 3.61/0.98  
% 3.61/0.98  --comb_res_mult                         3
% 3.61/0.98  --comb_sup_mult                         2
% 3.61/0.98  --comb_inst_mult                        10
% 3.61/0.98  
% 3.61/0.98  ------ Debug Options
% 3.61/0.98  
% 3.61/0.98  --dbg_backtrace                         false
% 3.61/0.98  --dbg_dump_prop_clauses                 false
% 3.61/0.98  --dbg_dump_prop_clauses_file            -
% 3.61/0.98  --dbg_out_stat                          false
% 3.61/0.98  ------ Parsing...
% 3.61/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.98  ------ Proving...
% 3.61/0.98  ------ Problem Properties 
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  clauses                                 12
% 3.61/0.98  conjectures                             4
% 3.61/0.98  EPR                                     4
% 3.61/0.98  Horn                                    12
% 3.61/0.98  unary                                   9
% 3.61/0.98  binary                                  0
% 3.61/0.98  lits                                    19
% 3.61/0.98  lits eq                                 3
% 3.61/0.98  fd_pure                                 0
% 3.61/0.98  fd_pseudo                               0
% 3.61/0.98  fd_cond                                 0
% 3.61/0.98  fd_pseudo_cond                          0
% 3.61/0.98  AC symbols                              0
% 3.61/0.98  
% 3.61/0.98  ------ Schedule dynamic 5 is on 
% 3.61/0.98  
% 3.61/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  ------ 
% 3.61/0.98  Current options:
% 3.61/0.98  ------ 
% 3.61/0.98  
% 3.61/0.98  ------ Input Options
% 3.61/0.98  
% 3.61/0.98  --out_options                           all
% 3.61/0.98  --tptp_safe_out                         true
% 3.61/0.98  --problem_path                          ""
% 3.61/0.98  --include_path                          ""
% 3.61/0.98  --clausifier                            res/vclausify_rel
% 3.61/0.98  --clausifier_options                    ""
% 3.61/0.98  --stdin                                 false
% 3.61/0.98  --stats_out                             all
% 3.61/0.98  
% 3.61/0.98  ------ General Options
% 3.61/0.98  
% 3.61/0.98  --fof                                   false
% 3.61/0.98  --time_out_real                         305.
% 3.61/0.98  --time_out_virtual                      -1.
% 3.61/0.98  --symbol_type_check                     false
% 3.61/0.98  --clausify_out                          false
% 3.61/0.98  --sig_cnt_out                           false
% 3.61/0.98  --trig_cnt_out                          false
% 3.61/0.98  --trig_cnt_out_tolerance                1.
% 3.61/0.98  --trig_cnt_out_sk_spl                   false
% 3.61/0.98  --abstr_cl_out                          false
% 3.61/0.98  
% 3.61/0.98  ------ Global Options
% 3.61/0.98  
% 3.61/0.98  --schedule                              default
% 3.61/0.98  --add_important_lit                     false
% 3.61/0.98  --prop_solver_per_cl                    1000
% 3.61/0.98  --min_unsat_core                        false
% 3.61/0.98  --soft_assumptions                      false
% 3.61/0.98  --soft_lemma_size                       3
% 3.61/0.98  --prop_impl_unit_size                   0
% 3.61/0.98  --prop_impl_unit                        []
% 3.61/0.98  --share_sel_clauses                     true
% 3.61/0.98  --reset_solvers                         false
% 3.61/0.98  --bc_imp_inh                            [conj_cone]
% 3.61/0.98  --conj_cone_tolerance                   3.
% 3.61/0.98  --extra_neg_conj                        none
% 3.61/0.98  --large_theory_mode                     true
% 3.61/0.98  --prolific_symb_bound                   200
% 3.61/0.98  --lt_threshold                          2000
% 3.61/0.98  --clause_weak_htbl                      true
% 3.61/0.98  --gc_record_bc_elim                     false
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing Options
% 3.61/0.98  
% 3.61/0.98  --preprocessing_flag                    true
% 3.61/0.98  --time_out_prep_mult                    0.1
% 3.61/0.98  --splitting_mode                        input
% 3.61/0.98  --splitting_grd                         true
% 3.61/0.98  --splitting_cvd                         false
% 3.61/0.98  --splitting_cvd_svl                     false
% 3.61/0.98  --splitting_nvd                         32
% 3.61/0.98  --sub_typing                            true
% 3.61/0.98  --prep_gs_sim                           true
% 3.61/0.98  --prep_unflatten                        true
% 3.61/0.98  --prep_res_sim                          true
% 3.61/0.98  --prep_upred                            true
% 3.61/0.98  --prep_sem_filter                       exhaustive
% 3.61/0.98  --prep_sem_filter_out                   false
% 3.61/0.98  --pred_elim                             true
% 3.61/0.98  --res_sim_input                         true
% 3.61/0.98  --eq_ax_congr_red                       true
% 3.61/0.98  --pure_diseq_elim                       true
% 3.61/0.98  --brand_transform                       false
% 3.61/0.98  --non_eq_to_eq                          false
% 3.61/0.98  --prep_def_merge                        true
% 3.61/0.98  --prep_def_merge_prop_impl              false
% 3.61/0.98  --prep_def_merge_mbd                    true
% 3.61/0.98  --prep_def_merge_tr_red                 false
% 3.61/0.98  --prep_def_merge_tr_cl                  false
% 3.61/0.98  --smt_preprocessing                     true
% 3.61/0.98  --smt_ac_axioms                         fast
% 3.61/0.98  --preprocessed_out                      false
% 3.61/0.98  --preprocessed_stats                    false
% 3.61/0.98  
% 3.61/0.98  ------ Abstraction refinement Options
% 3.61/0.98  
% 3.61/0.98  --abstr_ref                             []
% 3.61/0.98  --abstr_ref_prep                        false
% 3.61/0.98  --abstr_ref_until_sat                   false
% 3.61/0.98  --abstr_ref_sig_restrict                funpre
% 3.61/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.98  --abstr_ref_under                       []
% 3.61/0.98  
% 3.61/0.98  ------ SAT Options
% 3.61/0.98  
% 3.61/0.98  --sat_mode                              false
% 3.61/0.98  --sat_fm_restart_options                ""
% 3.61/0.98  --sat_gr_def                            false
% 3.61/0.98  --sat_epr_types                         true
% 3.61/0.98  --sat_non_cyclic_types                  false
% 3.61/0.98  --sat_finite_models                     false
% 3.61/0.98  --sat_fm_lemmas                         false
% 3.61/0.98  --sat_fm_prep                           false
% 3.61/0.98  --sat_fm_uc_incr                        true
% 3.61/0.98  --sat_out_model                         small
% 3.61/0.98  --sat_out_clauses                       false
% 3.61/0.98  
% 3.61/0.98  ------ QBF Options
% 3.61/0.98  
% 3.61/0.98  --qbf_mode                              false
% 3.61/0.98  --qbf_elim_univ                         false
% 3.61/0.98  --qbf_dom_inst                          none
% 3.61/0.98  --qbf_dom_pre_inst                      false
% 3.61/0.98  --qbf_sk_in                             false
% 3.61/0.98  --qbf_pred_elim                         true
% 3.61/0.98  --qbf_split                             512
% 3.61/0.98  
% 3.61/0.98  ------ BMC1 Options
% 3.61/0.98  
% 3.61/0.98  --bmc1_incremental                      false
% 3.61/0.98  --bmc1_axioms                           reachable_all
% 3.61/0.98  --bmc1_min_bound                        0
% 3.61/0.98  --bmc1_max_bound                        -1
% 3.61/0.98  --bmc1_max_bound_default                -1
% 3.61/0.98  --bmc1_symbol_reachability              true
% 3.61/0.98  --bmc1_property_lemmas                  false
% 3.61/0.98  --bmc1_k_induction                      false
% 3.61/0.98  --bmc1_non_equiv_states                 false
% 3.61/0.98  --bmc1_deadlock                         false
% 3.61/0.98  --bmc1_ucm                              false
% 3.61/0.98  --bmc1_add_unsat_core                   none
% 3.61/0.98  --bmc1_unsat_core_children              false
% 3.61/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.98  --bmc1_out_stat                         full
% 3.61/0.98  --bmc1_ground_init                      false
% 3.61/0.98  --bmc1_pre_inst_next_state              false
% 3.61/0.98  --bmc1_pre_inst_state                   false
% 3.61/0.98  --bmc1_pre_inst_reach_state             false
% 3.61/0.98  --bmc1_out_unsat_core                   false
% 3.61/0.98  --bmc1_aig_witness_out                  false
% 3.61/0.98  --bmc1_verbose                          false
% 3.61/0.98  --bmc1_dump_clauses_tptp                false
% 3.61/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.98  --bmc1_dump_file                        -
% 3.61/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.98  --bmc1_ucm_extend_mode                  1
% 3.61/0.98  --bmc1_ucm_init_mode                    2
% 3.61/0.98  --bmc1_ucm_cone_mode                    none
% 3.61/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.98  --bmc1_ucm_relax_model                  4
% 3.61/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.98  --bmc1_ucm_layered_model                none
% 3.61/0.98  --bmc1_ucm_max_lemma_size               10
% 3.61/0.98  
% 3.61/0.98  ------ AIG Options
% 3.61/0.98  
% 3.61/0.98  --aig_mode                              false
% 3.61/0.98  
% 3.61/0.98  ------ Instantiation Options
% 3.61/0.98  
% 3.61/0.98  --instantiation_flag                    true
% 3.61/0.98  --inst_sos_flag                         true
% 3.61/0.98  --inst_sos_phase                        true
% 3.61/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.98  --inst_lit_sel_side                     none
% 3.61/0.98  --inst_solver_per_active                1400
% 3.61/0.98  --inst_solver_calls_frac                1.
% 3.61/0.98  --inst_passive_queue_type               priority_queues
% 3.61/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.98  --inst_passive_queues_freq              [25;2]
% 3.61/0.98  --inst_dismatching                      true
% 3.61/0.98  --inst_eager_unprocessed_to_passive     true
% 3.61/0.98  --inst_prop_sim_given                   true
% 3.61/0.98  --inst_prop_sim_new                     false
% 3.61/0.98  --inst_subs_new                         false
% 3.61/0.98  --inst_eq_res_simp                      false
% 3.61/0.98  --inst_subs_given                       false
% 3.61/0.98  --inst_orphan_elimination               true
% 3.61/0.98  --inst_learning_loop_flag               true
% 3.61/0.98  --inst_learning_start                   3000
% 3.61/0.98  --inst_learning_factor                  2
% 3.61/0.98  --inst_start_prop_sim_after_learn       3
% 3.61/0.98  --inst_sel_renew                        solver
% 3.61/0.98  --inst_lit_activity_flag                true
% 3.61/0.98  --inst_restr_to_given                   false
% 3.61/0.98  --inst_activity_threshold               500
% 3.61/0.98  --inst_out_proof                        true
% 3.61/0.98  
% 3.61/0.98  ------ Resolution Options
% 3.61/0.98  
% 3.61/0.98  --resolution_flag                       false
% 3.61/0.98  --res_lit_sel                           adaptive
% 3.61/0.98  --res_lit_sel_side                      none
% 3.61/0.98  --res_ordering                          kbo
% 3.61/0.98  --res_to_prop_solver                    active
% 3.61/0.98  --res_prop_simpl_new                    false
% 3.61/0.98  --res_prop_simpl_given                  true
% 3.61/0.98  --res_passive_queue_type                priority_queues
% 3.61/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.98  --res_passive_queues_freq               [15;5]
% 3.61/0.98  --res_forward_subs                      full
% 3.61/0.98  --res_backward_subs                     full
% 3.61/0.98  --res_forward_subs_resolution           true
% 3.61/0.98  --res_backward_subs_resolution          true
% 3.61/0.98  --res_orphan_elimination                true
% 3.61/0.98  --res_time_limit                        2.
% 3.61/0.98  --res_out_proof                         true
% 3.61/0.98  
% 3.61/0.98  ------ Superposition Options
% 3.61/0.98  
% 3.61/0.98  --superposition_flag                    true
% 3.61/0.98  --sup_passive_queue_type                priority_queues
% 3.61/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.98  --demod_completeness_check              fast
% 3.61/0.98  --demod_use_ground                      true
% 3.61/0.98  --sup_to_prop_solver                    passive
% 3.61/0.98  --sup_prop_simpl_new                    true
% 3.61/0.98  --sup_prop_simpl_given                  true
% 3.61/0.98  --sup_fun_splitting                     true
% 3.61/0.98  --sup_smt_interval                      50000
% 3.61/0.98  
% 3.61/0.98  ------ Superposition Simplification Setup
% 3.61/0.98  
% 3.61/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.61/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.61/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.61/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.61/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.61/0.98  --sup_immed_triv                        [TrivRules]
% 3.61/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.98  --sup_immed_bw_main                     []
% 3.61/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.61/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.98  --sup_input_bw                          []
% 3.61/0.98  
% 3.61/0.98  ------ Combination Options
% 3.61/0.98  
% 3.61/0.98  --comb_res_mult                         3
% 3.61/0.98  --comb_sup_mult                         2
% 3.61/0.98  --comb_inst_mult                        10
% 3.61/0.98  
% 3.61/0.98  ------ Debug Options
% 3.61/0.98  
% 3.61/0.98  --dbg_backtrace                         false
% 3.61/0.98  --dbg_dump_prop_clauses                 false
% 3.61/0.98  --dbg_dump_prop_clauses_file            -
% 3.61/0.98  --dbg_out_stat                          false
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  ------ Proving...
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  % SZS status Theorem for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98   Resolution empty clause
% 3.61/0.98  
% 3.61/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  fof(f7,axiom,(
% 3.61/0.98    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f38,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.61/0.98    inference(cnf_transformation,[],[f7])).
% 3.61/0.98  
% 3.61/0.98  fof(f14,axiom,(
% 3.61/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f45,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f14])).
% 3.61/0.98  
% 3.61/0.98  fof(f62,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.61/0.98    inference(definition_unfolding,[],[f45,f59])).
% 3.61/0.98  
% 3.61/0.98  fof(f1,axiom,(
% 3.61/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f32,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f1])).
% 3.61/0.98  
% 3.61/0.98  fof(f15,axiom,(
% 3.61/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f46,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f15])).
% 3.61/0.98  
% 3.61/0.98  fof(f8,axiom,(
% 3.61/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f39,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f8])).
% 3.61/0.98  
% 3.61/0.98  fof(f9,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f40,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f9])).
% 3.61/0.98  
% 3.61/0.98  fof(f10,axiom,(
% 3.61/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f41,plain,(
% 3.61/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f10])).
% 3.61/0.98  
% 3.61/0.98  fof(f11,axiom,(
% 3.61/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f42,plain,(
% 3.61/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f11])).
% 3.61/0.98  
% 3.61/0.98  fof(f12,axiom,(
% 3.61/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f43,plain,(
% 3.61/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f12])).
% 3.61/0.98  
% 3.61/0.98  fof(f13,axiom,(
% 3.61/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f44,plain,(
% 3.61/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f13])).
% 3.61/0.98  
% 3.61/0.98  fof(f55,plain,(
% 3.61/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.61/0.98    inference(definition_unfolding,[],[f43,f44])).
% 3.61/0.98  
% 3.61/0.98  fof(f56,plain,(
% 3.61/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.61/0.98    inference(definition_unfolding,[],[f42,f55])).
% 3.61/0.98  
% 3.61/0.98  fof(f57,plain,(
% 3.61/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.61/0.98    inference(definition_unfolding,[],[f41,f56])).
% 3.61/0.98  
% 3.61/0.98  fof(f58,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.61/0.98    inference(definition_unfolding,[],[f40,f57])).
% 3.61/0.98  
% 3.61/0.98  fof(f59,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.61/0.98    inference(definition_unfolding,[],[f39,f58])).
% 3.61/0.98  
% 3.61/0.98  fof(f60,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.61/0.98    inference(definition_unfolding,[],[f46,f59])).
% 3.61/0.98  
% 3.61/0.98  fof(f61,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.61/0.98    inference(definition_unfolding,[],[f32,f60])).
% 3.61/0.98  
% 3.61/0.98  fof(f68,plain,(
% 3.61/0.98    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0) )),
% 3.61/0.98    inference(definition_unfolding,[],[f38,f62,f60,f61])).
% 3.61/0.98  
% 3.61/0.98  fof(f5,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f36,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f5])).
% 3.61/0.98  
% 3.61/0.98  fof(f66,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 3.61/0.98    inference(definition_unfolding,[],[f36,f62,f60,f60,f62])).
% 3.61/0.98  
% 3.61/0.98  fof(f2,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f33,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f2])).
% 3.61/0.98  
% 3.61/0.98  fof(f63,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) )),
% 3.61/0.98    inference(definition_unfolding,[],[f33,f60,f60,f60,f60])).
% 3.61/0.98  
% 3.61/0.98  fof(f6,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f37,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f6])).
% 3.61/0.98  
% 3.61/0.98  fof(f67,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) )),
% 3.61/0.98    inference(definition_unfolding,[],[f37,f61,f60,f60,f61])).
% 3.61/0.98  
% 3.61/0.98  fof(f18,axiom,(
% 3.61/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f24,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.61/0.98    inference(ennf_transformation,[],[f18])).
% 3.61/0.98  
% 3.61/0.98  fof(f25,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.61/0.98    inference(flattening,[],[f24])).
% 3.61/0.98  
% 3.61/0.98  fof(f50,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f25])).
% 3.61/0.98  
% 3.61/0.98  fof(f17,axiom,(
% 3.61/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f23,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.61/0.98    inference(ennf_transformation,[],[f17])).
% 3.61/0.98  
% 3.61/0.98  fof(f49,plain,(
% 3.61/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f23])).
% 3.61/0.98  
% 3.61/0.98  fof(f16,axiom,(
% 3.61/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f27,plain,(
% 3.61/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.61/0.98    inference(nnf_transformation,[],[f16])).
% 3.61/0.98  
% 3.61/0.98  fof(f48,plain,(
% 3.61/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f27])).
% 3.61/0.98  
% 3.61/0.98  fof(f4,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f21,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.61/0.98    inference(ennf_transformation,[],[f4])).
% 3.61/0.98  
% 3.61/0.98  fof(f22,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.61/0.98    inference(flattening,[],[f21])).
% 3.61/0.98  
% 3.61/0.98  fof(f35,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f22])).
% 3.61/0.98  
% 3.61/0.98  fof(f65,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.61/0.98    inference(definition_unfolding,[],[f35,f60])).
% 3.61/0.98  
% 3.61/0.98  fof(f19,conjecture,(
% 3.61/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f20,negated_conjecture,(
% 3.61/0.98    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 3.61/0.98    inference(negated_conjecture,[],[f19])).
% 3.61/0.98  
% 3.61/0.98  fof(f26,plain,(
% 3.61/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.61/0.98    inference(ennf_transformation,[],[f20])).
% 3.61/0.98  
% 3.61/0.98  fof(f30,plain,(
% 3.61/0.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,sK2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,sK2))) & v1_relat_1(sK2))) )),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f29,plain,(
% 3.61/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(X0,sK1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))) )),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f28,plain,(
% 3.61/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f31,plain,(
% 3.61/0.98    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29,f28])).
% 3.61/0.98  
% 3.61/0.98  fof(f54,plain,(
% 3.61/0.98    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 3.61/0.98    inference(cnf_transformation,[],[f31])).
% 3.61/0.98  
% 3.61/0.98  fof(f69,plain,(
% 3.61/0.98    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 3.61/0.98    inference(definition_unfolding,[],[f54,f60,f60])).
% 3.61/0.98  
% 3.61/0.98  fof(f51,plain,(
% 3.61/0.98    v1_relat_1(sK0)),
% 3.61/0.98    inference(cnf_transformation,[],[f31])).
% 3.61/0.98  
% 3.61/0.98  fof(f52,plain,(
% 3.61/0.98    v1_relat_1(sK1)),
% 3.61/0.98    inference(cnf_transformation,[],[f31])).
% 3.61/0.98  
% 3.61/0.98  fof(f3,axiom,(
% 3.61/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f34,plain,(
% 3.61/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f3])).
% 3.61/0.98  
% 3.61/0.98  fof(f64,plain,(
% 3.61/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.61/0.98    inference(definition_unfolding,[],[f34,f60])).
% 3.61/0.98  
% 3.61/0.98  fof(f53,plain,(
% 3.61/0.98    v1_relat_1(sK2)),
% 3.61/0.98    inference(cnf_transformation,[],[f31])).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5,plain,
% 3.61/0.98      ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
% 3.61/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3,plain,
% 3.61/0.98      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.61/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_395,plain,
% 3.61/0.98      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1205,plain,
% 3.61/0.98      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))),X1) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_5,c_395]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_0,plain,
% 3.61/0.98      ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 3.61/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_745,plain,
% 3.61/0.98      ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4,plain,
% 3.61/0.98      ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
% 3.61/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_398,plain,
% 3.61/0.98      ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
% 3.61/0.98      inference(light_normalisation,[status(thm)],[c_4,c_0]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_753,plain,
% 3.61/0.98      ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.61/0.98      inference(light_normalisation,[status(thm)],[c_745,c_398]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1207,plain,
% 3.61/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
% 3.61/0.98      inference(light_normalisation,[status(thm)],[c_1205,c_753]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9,plain,
% 3.61/0.98      ( ~ r1_tarski(X0,X1)
% 3.61/0.98      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.61/0.98      | ~ v1_relat_1(X0)
% 3.61/0.98      | ~ v1_relat_1(X1)
% 3.61/0.98      | ~ v1_relat_1(X2) ),
% 3.61/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_8,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_6,plain,
% 3.61/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_67,plain,
% 3.61/0.98      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.61/0.98      | ~ r1_tarski(X0,X1)
% 3.61/0.98      | ~ v1_relat_1(X1)
% 3.61/0.98      | ~ v1_relat_1(X2) ),
% 3.61/0.98      inference(global_propositional_subsumption,[status(thm)],[c_9,c_8,c_6]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_68,plain,
% 3.61/0.98      ( ~ r1_tarski(X0,X1)
% 3.61/0.98      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
% 3.61/0.98      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v1_relat_1(X2) ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_67]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_390,plain,
% 3.61/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.61/0.99      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) = iProver_top
% 3.61/0.99      | v1_relat_1(X1) != iProver_top
% 3.61/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1)
% 3.61/0.99      | ~ r1_tarski(X0,X2)
% 3.61/0.99      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_396,plain,
% 3.61/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.61/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.61/0.99      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10,negated_conjecture,
% 3.61/0.99      ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_394,plain,
% 3.61/0.99      ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_805,plain,
% 3.61/0.99      ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) != iProver_top
% 3.61/0.99      | r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_396,c_394]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_13,negated_conjecture,
% 3.61/0.99      ( v1_relat_1(sK0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_14,plain,
% 3.61/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12,negated_conjecture,
% 3.61/0.99      ( v1_relat_1(sK1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_15,plain,
% 3.61/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_512,plain,
% 3.61/0.99      ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,X0))
% 3.61/0.99      | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),X0)
% 3.61/0.99      | ~ v1_relat_1(X0)
% 3.61/0.99      | ~ v1_relat_1(sK0) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_68]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_513,plain,
% 3.61/0.99      ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,X0)) = iProver_top
% 3.61/0.99      | r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),X0) != iProver_top
% 3.61/0.99      | v1_relat_1(X0) != iProver_top
% 3.61/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_515,plain,
% 3.61/0.99      ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) = iProver_top
% 3.61/0.99      | r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) != iProver_top
% 3.61/0.99      | v1_relat_1(sK1) != iProver_top
% 3.61/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_513]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1,plain,
% 3.61/0.99      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_821,plain,
% 3.61/0.99      ( r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_822,plain,
% 3.61/0.99      ( r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_870,plain,
% 3.61/0.99      ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_805,c_14,c_15,c_515,c_822]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_874,plain,
% 3.61/0.99      ( r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) != iProver_top
% 3.61/0.99      | v1_relat_1(sK2) != iProver_top
% 3.61/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_390,c_870]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11,negated_conjecture,
% 3.61/0.99      ( v1_relat_1(sK2) ),
% 3.61/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_16,plain,
% 3.61/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_421,plain,
% 3.61/0.99      ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
% 3.61/0.99      | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
% 3.61/0.99      | ~ v1_relat_1(sK2)
% 3.61/0.99      | ~ v1_relat_1(sK0) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_68]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_422,plain,
% 3.61/0.99      ( r1_tarski(k5_relat_1(sK0,k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) = iProver_top
% 3.61/0.99      | r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) != iProver_top
% 3.61/0.99      | v1_relat_1(sK2) != iProver_top
% 3.61/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_945,plain,
% 3.61/0.99      ( r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) != iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_874,c_14,c_15,c_16,c_422,c_515,c_805,c_822]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1529,plain,
% 3.61/0.99      ( $false ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1207,c_945]) ).
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  ------                               Statistics
% 3.61/0.99  
% 3.61/0.99  ------ General
% 3.61/0.99  
% 3.61/0.99  abstr_ref_over_cycles:                  0
% 3.61/0.99  abstr_ref_under_cycles:                 0
% 3.61/0.99  gc_basic_clause_elim:                   0
% 3.61/0.99  forced_gc_time:                         0
% 3.61/0.99  parsing_time:                           0.009
% 3.61/0.99  unif_index_cands_time:                  0.
% 3.61/0.99  unif_index_add_time:                    0.
% 3.61/0.99  orderings_time:                         0.
% 3.61/0.99  out_proof_time:                         0.01
% 3.61/0.99  total_time:                             0.259
% 3.61/0.99  num_of_symbols:                         43
% 3.61/0.99  num_of_terms:                           2383
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing
% 3.61/0.99  
% 3.61/0.99  num_of_splits:                          0
% 3.61/0.99  num_of_split_atoms:                     0
% 3.61/0.99  num_of_reused_defs:                     0
% 3.61/0.99  num_eq_ax_congr_red:                    2
% 3.61/0.99  num_of_sem_filtered_clauses:            1
% 3.61/0.99  num_of_subtypes:                        0
% 3.61/0.99  monotx_restored_types:                  0
% 3.61/0.99  sat_num_of_epr_types:                   0
% 3.61/0.99  sat_num_of_non_cyclic_types:            0
% 3.61/0.99  sat_guarded_non_collapsed_types:        0
% 3.61/0.99  num_pure_diseq_elim:                    0
% 3.61/0.99  simp_replaced_by:                       0
% 3.61/0.99  res_preprocessed:                       69
% 3.61/0.99  prep_upred:                             0
% 3.61/0.99  prep_unflattend:                        0
% 3.61/0.99  smt_new_axioms:                         0
% 3.61/0.99  pred_elim_cands:                        2
% 3.61/0.99  pred_elim:                              1
% 3.61/0.99  pred_elim_cl:                           2
% 3.61/0.99  pred_elim_cycles:                       3
% 3.61/0.99  merged_defs:                            2
% 3.61/0.99  merged_defs_ncl:                        0
% 3.61/0.99  bin_hyper_res:                          3
% 3.61/0.99  prep_cycles:                            4
% 3.61/0.99  pred_elim_time:                         0.
% 3.61/0.99  splitting_time:                         0.
% 3.61/0.99  sem_filter_time:                        0.
% 3.61/0.99  monotx_time:                            0.
% 3.61/0.99  subtype_inf_time:                       0.
% 3.61/0.99  
% 3.61/0.99  ------ Problem properties
% 3.61/0.99  
% 3.61/0.99  clauses:                                12
% 3.61/0.99  conjectures:                            4
% 3.61/0.99  epr:                                    4
% 3.61/0.99  horn:                                   12
% 3.61/0.99  ground:                                 4
% 3.61/0.99  unary:                                  9
% 3.61/0.99  binary:                                 0
% 3.61/0.99  lits:                                   19
% 3.61/0.99  lits_eq:                                3
% 3.61/0.99  fd_pure:                                0
% 3.61/0.99  fd_pseudo:                              0
% 3.61/0.99  fd_cond:                                0
% 3.61/0.99  fd_pseudo_cond:                         0
% 3.61/0.99  ac_symbols:                             0
% 3.61/0.99  
% 3.61/0.99  ------ Propositional Solver
% 3.61/0.99  
% 3.61/0.99  prop_solver_calls:                      31
% 3.61/0.99  prop_fast_solver_calls:                 349
% 3.61/0.99  smt_solver_calls:                       0
% 3.61/0.99  smt_fast_solver_calls:                  0
% 3.61/0.99  prop_num_of_clauses:                    695
% 3.61/0.99  prop_preprocess_simplified:             2115
% 3.61/0.99  prop_fo_subsumed:                       4
% 3.61/0.99  prop_solver_time:                       0.
% 3.61/0.99  smt_solver_time:                        0.
% 3.61/0.99  smt_fast_solver_time:                   0.
% 3.61/0.99  prop_fast_solver_time:                  0.
% 3.61/0.99  prop_unsat_core_time:                   0.
% 3.61/0.99  
% 3.61/0.99  ------ QBF
% 3.61/0.99  
% 3.61/0.99  qbf_q_res:                              0
% 3.61/0.99  qbf_num_tautologies:                    0
% 3.61/0.99  qbf_prep_cycles:                        0
% 3.61/0.99  
% 3.61/0.99  ------ BMC1
% 3.61/0.99  
% 3.61/0.99  bmc1_current_bound:                     -1
% 3.61/0.99  bmc1_last_solved_bound:                 -1
% 3.61/0.99  bmc1_unsat_core_size:                   -1
% 3.61/0.99  bmc1_unsat_core_parents_size:           -1
% 3.61/0.99  bmc1_merge_next_fun:                    0
% 3.61/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.61/0.99  
% 3.61/0.99  ------ Instantiation
% 3.61/0.99  
% 3.61/0.99  inst_num_of_clauses:                    196
% 3.61/0.99  inst_num_in_passive:                    35
% 3.61/0.99  inst_num_in_active:                     121
% 3.61/0.99  inst_num_in_unprocessed:                40
% 3.61/0.99  inst_num_of_loops:                      140
% 3.61/0.99  inst_num_of_learning_restarts:          0
% 3.61/0.99  inst_num_moves_active_passive:          14
% 3.61/0.99  inst_lit_activity:                      0
% 3.61/0.99  inst_lit_activity_moves:                0
% 3.61/0.99  inst_num_tautologies:                   0
% 3.61/0.99  inst_num_prop_implied:                  0
% 3.61/0.99  inst_num_existing_simplified:           0
% 3.61/0.99  inst_num_eq_res_simplified:             0
% 3.61/0.99  inst_num_child_elim:                    0
% 3.61/0.99  inst_num_of_dismatching_blockings:      54
% 3.61/0.99  inst_num_of_non_proper_insts:           224
% 3.61/0.99  inst_num_of_duplicates:                 0
% 3.61/0.99  inst_inst_num_from_inst_to_res:         0
% 3.61/0.99  inst_dismatching_checking_time:         0.
% 3.61/0.99  
% 3.61/0.99  ------ Resolution
% 3.61/0.99  
% 3.61/0.99  res_num_of_clauses:                     0
% 3.61/0.99  res_num_in_passive:                     0
% 3.61/0.99  res_num_in_active:                      0
% 3.61/0.99  res_num_of_loops:                       73
% 3.61/0.99  res_forward_subset_subsumed:            46
% 3.61/0.99  res_backward_subset_subsumed:           0
% 3.61/0.99  res_forward_subsumed:                   0
% 3.61/0.99  res_backward_subsumed:                  0
% 3.61/0.99  res_forward_subsumption_resolution:     0
% 3.61/0.99  res_backward_subsumption_resolution:    0
% 3.61/0.99  res_clause_to_clause_subsumption:       260
% 3.61/0.99  res_orphan_elimination:                 0
% 3.61/0.99  res_tautology_del:                      35
% 3.61/0.99  res_num_eq_res_simplified:              0
% 3.61/0.99  res_num_sel_changes:                    0
% 3.61/0.99  res_moves_from_active_to_pass:          0
% 3.61/0.99  
% 3.61/0.99  ------ Superposition
% 3.61/0.99  
% 3.61/0.99  sup_time_total:                         0.
% 3.61/0.99  sup_time_generating:                    0.
% 3.61/0.99  sup_time_sim_full:                      0.
% 3.61/0.99  sup_time_sim_immed:                     0.
% 3.61/0.99  
% 3.61/0.99  sup_num_of_clauses:                     43
% 3.61/0.99  sup_num_in_active:                      27
% 3.61/0.99  sup_num_in_passive:                     16
% 3.61/0.99  sup_num_of_loops:                       26
% 3.61/0.99  sup_fw_superposition:                   67
% 3.61/0.99  sup_bw_superposition:                   24
% 3.61/0.99  sup_immediate_simplified:               32
% 3.61/0.99  sup_given_eliminated:                   0
% 3.61/0.99  comparisons_done:                       0
% 3.61/0.99  comparisons_avoided:                    0
% 3.61/0.99  
% 3.61/0.99  ------ Simplifications
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  sim_fw_subset_subsumed:                 0
% 3.61/0.99  sim_bw_subset_subsumed:                 0
% 3.61/0.99  sim_fw_subsumed:                        7
% 3.61/0.99  sim_bw_subsumed:                        0
% 3.61/0.99  sim_fw_subsumption_res:                 0
% 3.61/0.99  sim_bw_subsumption_res:                 0
% 3.61/0.99  sim_tautology_del:                      0
% 3.61/0.99  sim_eq_tautology_del:                   0
% 3.61/0.99  sim_eq_res_simp:                        0
% 3.61/0.99  sim_fw_demodulated:                     18
% 3.61/0.99  sim_bw_demodulated:                     0
% 3.61/0.99  sim_light_normalised:                   9
% 3.61/0.99  sim_joinable_taut:                      0
% 3.61/0.99  sim_joinable_simp:                      0
% 3.61/0.99  sim_ac_normalised:                      0
% 3.61/0.99  sim_smt_subsumption:                    0
% 3.61/0.99  
%------------------------------------------------------------------------------

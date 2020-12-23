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
% DateTime   : Thu Dec  3 11:43:03 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 868 expanded)
%              Number of clauses        :   40 (  72 expanded)
%              Number of leaves         :   21 ( 276 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 (1174 expanded)
%              Number of equality atoms :   73 ( 739 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f59])).

fof(f67,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f37,f61,f59,f60])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f35,f61,f59,f59,f61])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f32,f59,f59,f59,f59])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(definition_unfolding,[],[f36,f60,f59,f59,f60])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29,f28])).

fof(f53,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f53,f59,f59])).

fof(f51,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f59])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_399,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1271,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_399])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_740,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_402,plain,
    ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
    inference(light_normalisation,[status(thm)],[c_4,c_0])).

cnf(c_748,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_740,c_402])).

cnf(c_1275,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1271,c_748])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_73,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_8,c_6])).

cnf(c_74,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_73])).

cnf(c_394,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_400,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_398,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_794,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_400,c_398])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_416,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK0))
    | r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_417,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) != iProver_top
    | r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) != iProver_top
    | r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_513,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(X0))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_514,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(X0)) = iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_516,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) = iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_762,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_763,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_884,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_794,c_14,c_16,c_417,c_516,c_763])).

cnf(c_888,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_394,c_884])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_424,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1))
    | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_425,plain,
    ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) = iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_998,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_888,c_14,c_15,c_16,c_417,c_425,c_516,c_763])).

cnf(c_1710,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1275,c_998])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:00:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.70/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.99  
% 3.70/0.99  ------  iProver source info
% 3.70/0.99  
% 3.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.99  git: non_committed_changes: false
% 3.70/0.99  git: last_make_outside_of_git: false
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    ""
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/0.99  --bmc1_deadlock                         false
% 3.70/0.99  --bmc1_ucm                              false
% 3.70/0.99  --bmc1_add_unsat_core                   none
% 3.70/0.99  --bmc1_unsat_core_children              false
% 3.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.99  --bmc1_out_stat                         full
% 3.70/0.99  --bmc1_ground_init                      false
% 3.70/0.99  --bmc1_pre_inst_next_state              false
% 3.70/0.99  --bmc1_pre_inst_state                   false
% 3.70/0.99  --bmc1_pre_inst_reach_state             false
% 3.70/0.99  --bmc1_out_unsat_core                   false
% 3.70/0.99  --bmc1_aig_witness_out                  false
% 3.70/0.99  --bmc1_verbose                          false
% 3.70/0.99  --bmc1_dump_clauses_tptp                false
% 3.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.99  --bmc1_dump_file                        -
% 3.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.99  --bmc1_ucm_extend_mode                  1
% 3.70/0.99  --bmc1_ucm_init_mode                    2
% 3.70/0.99  --bmc1_ucm_cone_mode                    none
% 3.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.99  --bmc1_ucm_relax_model                  4
% 3.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.99  --bmc1_ucm_layered_model                none
% 3.70/0.99  --bmc1_ucm_max_lemma_size               10
% 3.70/0.99  
% 3.70/0.99  ------ AIG Options
% 3.70/0.99  
% 3.70/0.99  --aig_mode                              false
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation Options
% 3.70/0.99  
% 3.70/0.99  --instantiation_flag                    true
% 3.70/0.99  --inst_sos_flag                         true
% 3.70/0.99  --inst_sos_phase                        true
% 3.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel_side                     num_symb
% 3.70/0.99  --inst_solver_per_active                1400
% 3.70/0.99  --inst_solver_calls_frac                1.
% 3.70/0.99  --inst_passive_queue_type               priority_queues
% 3.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.99  --inst_passive_queues_freq              [25;2]
% 3.70/0.99  --inst_dismatching                      true
% 3.70/0.99  --inst_eager_unprocessed_to_passive     true
% 3.70/0.99  --inst_prop_sim_given                   true
% 3.70/0.99  --inst_prop_sim_new                     false
% 3.70/0.99  --inst_subs_new                         false
% 3.70/0.99  --inst_eq_res_simp                      false
% 3.70/0.99  --inst_subs_given                       false
% 3.70/0.99  --inst_orphan_elimination               true
% 3.70/0.99  --inst_learning_loop_flag               true
% 3.70/0.99  --inst_learning_start                   3000
% 3.70/0.99  --inst_learning_factor                  2
% 3.70/0.99  --inst_start_prop_sim_after_learn       3
% 3.70/0.99  --inst_sel_renew                        solver
% 3.70/0.99  --inst_lit_activity_flag                true
% 3.70/0.99  --inst_restr_to_given                   false
% 3.70/0.99  --inst_activity_threshold               500
% 3.70/0.99  --inst_out_proof                        true
% 3.70/0.99  
% 3.70/0.99  ------ Resolution Options
% 3.70/0.99  
% 3.70/0.99  --resolution_flag                       true
% 3.70/0.99  --res_lit_sel                           adaptive
% 3.70/0.99  --res_lit_sel_side                      none
% 3.70/0.99  --res_ordering                          kbo
% 3.70/0.99  --res_to_prop_solver                    active
% 3.70/0.99  --res_prop_simpl_new                    false
% 3.70/0.99  --res_prop_simpl_given                  true
% 3.70/0.99  --res_passive_queue_type                priority_queues
% 3.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     true
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_input_bw                          []
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  ------ Parsing...
% 3.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  ------ Proving...
% 3.70/0.99  ------ Problem Properties 
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  clauses                                 12
% 3.70/0.99  conjectures                             3
% 3.70/0.99  EPR                                     3
% 3.70/0.99  Horn                                    12
% 3.70/0.99  unary                                   8
% 3.70/0.99  binary                                  0
% 3.70/0.99  lits                                    20
% 3.70/0.99  lits eq                                 3
% 3.70/0.99  fd_pure                                 0
% 3.70/0.99  fd_pseudo                               0
% 3.70/0.99  fd_cond                                 0
% 3.70/0.99  fd_pseudo_cond                          0
% 3.70/0.99  AC symbols                              0
% 3.70/0.99  
% 3.70/0.99  ------ Schedule dynamic 5 is on 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  Current options:
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    ""
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         true
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     none
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       false
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     true
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_input_bw                          []
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ Proving...
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS status Theorem for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00   Resolution empty clause
% 3.70/1.00  
% 3.70/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  fof(f7,axiom,(
% 3.70/1.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f37,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.70/1.00    inference(cnf_transformation,[],[f7])).
% 3.70/1.00  
% 3.70/1.00  fof(f14,axiom,(
% 3.70/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f44,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f14])).
% 3.70/1.00  
% 3.70/1.00  fof(f61,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.70/1.00    inference(definition_unfolding,[],[f44,f58])).
% 3.70/1.00  
% 3.70/1.00  fof(f1,axiom,(
% 3.70/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f31,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f1])).
% 3.70/1.00  
% 3.70/1.00  fof(f15,axiom,(
% 3.70/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f45,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f15])).
% 3.70/1.00  
% 3.70/1.00  fof(f8,axiom,(
% 3.70/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f38,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f8])).
% 3.70/1.00  
% 3.70/1.00  fof(f9,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f39,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f9])).
% 3.70/1.00  
% 3.70/1.00  fof(f10,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f40,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f10])).
% 3.70/1.00  
% 3.70/1.00  fof(f11,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f41,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f11])).
% 3.70/1.00  
% 3.70/1.00  fof(f12,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f42,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f12])).
% 3.70/1.00  
% 3.70/1.00  fof(f13,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f43,plain,(
% 3.70/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f13])).
% 3.70/1.00  
% 3.70/1.00  fof(f54,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f42,f43])).
% 3.70/1.00  
% 3.70/1.00  fof(f55,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f41,f54])).
% 3.70/1.00  
% 3.70/1.00  fof(f56,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f40,f55])).
% 3.70/1.00  
% 3.70/1.00  fof(f57,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f39,f56])).
% 3.70/1.00  
% 3.70/1.00  fof(f58,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f38,f57])).
% 3.70/1.00  
% 3.70/1.00  fof(f59,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.70/1.00    inference(definition_unfolding,[],[f45,f58])).
% 3.70/1.00  
% 3.70/1.00  fof(f60,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.70/1.00    inference(definition_unfolding,[],[f31,f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f67,plain,(
% 3.70/1.00    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0) )),
% 3.70/1.00    inference(definition_unfolding,[],[f37,f61,f59,f60])).
% 3.70/1.00  
% 3.70/1.00  fof(f5,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f35,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f5])).
% 3.70/1.00  
% 3.70/1.00  fof(f65,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 3.70/1.00    inference(definition_unfolding,[],[f35,f61,f59,f59,f61])).
% 3.70/1.00  
% 3.70/1.00  fof(f2,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f32,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f2])).
% 3.70/1.00  
% 3.70/1.00  fof(f62,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) )),
% 3.70/1.00    inference(definition_unfolding,[],[f32,f59,f59,f59,f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f6,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f36,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f6])).
% 3.70/1.00  
% 3.70/1.00  fof(f66,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))) )),
% 3.70/1.00    inference(definition_unfolding,[],[f36,f60,f59,f59,f60])).
% 3.70/1.00  
% 3.70/1.00  fof(f18,axiom,(
% 3.70/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f24,plain,(
% 3.70/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.70/1.00    inference(ennf_transformation,[],[f18])).
% 3.70/1.00  
% 3.70/1.00  fof(f25,plain,(
% 3.70/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.70/1.00    inference(flattening,[],[f24])).
% 3.70/1.00  
% 3.70/1.00  fof(f50,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f25])).
% 3.70/1.00  
% 3.70/1.00  fof(f17,axiom,(
% 3.70/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f23,plain,(
% 3.70/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.70/1.00    inference(ennf_transformation,[],[f17])).
% 3.70/1.00  
% 3.70/1.00  fof(f48,plain,(
% 3.70/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f23])).
% 3.70/1.00  
% 3.70/1.00  fof(f16,axiom,(
% 3.70/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f27,plain,(
% 3.70/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.70/1.00    inference(nnf_transformation,[],[f16])).
% 3.70/1.00  
% 3.70/1.00  fof(f47,plain,(
% 3.70/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f27])).
% 3.70/1.00  
% 3.70/1.00  fof(f4,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f21,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.70/1.00    inference(ennf_transformation,[],[f4])).
% 3.70/1.00  
% 3.70/1.00  fof(f22,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.70/1.00    inference(flattening,[],[f21])).
% 3.70/1.00  
% 3.70/1.00  fof(f34,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f22])).
% 3.70/1.00  
% 3.70/1.00  fof(f64,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f34,f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f19,conjecture,(
% 3.70/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f20,negated_conjecture,(
% 3.70/1.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 3.70/1.00    inference(negated_conjecture,[],[f19])).
% 3.70/1.00  
% 3.70/1.00  fof(f26,plain,(
% 3.70/1.00    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.70/1.00    inference(ennf_transformation,[],[f20])).
% 3.70/1.00  
% 3.70/1.00  fof(f29,plain,(
% 3.70/1.00    ( ! [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f28,plain,(
% 3.70/1.00    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f30,plain,(
% 3.70/1.00    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29,f28])).
% 3.70/1.00  
% 3.70/1.00  fof(f53,plain,(
% 3.70/1.00    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 3.70/1.00    inference(cnf_transformation,[],[f30])).
% 3.70/1.00  
% 3.70/1.00  fof(f68,plain,(
% 3.70/1.00    ~r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))))),
% 3.70/1.00    inference(definition_unfolding,[],[f53,f59,f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f51,plain,(
% 3.70/1.00    v1_relat_1(sK0)),
% 3.70/1.00    inference(cnf_transformation,[],[f30])).
% 3.70/1.00  
% 3.70/1.00  fof(f3,axiom,(
% 3.70/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f33,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f3])).
% 3.70/1.00  
% 3.70/1.00  fof(f63,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.70/1.00    inference(definition_unfolding,[],[f33,f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f52,plain,(
% 3.70/1.00    v1_relat_1(sK1)),
% 3.70/1.00    inference(cnf_transformation,[],[f30])).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5,plain,
% 3.70/1.00      ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
% 3.70/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3,plain,
% 3.70/1.00      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_399,plain,
% 3.70/1.00      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1271,plain,
% 3.70/1.00      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))),X1) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_5,c_399]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_0,plain,
% 3.70/1.00      ( k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_740,plain,
% 3.70/1.00      ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4,plain,
% 3.70/1.00      ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_402,plain,
% 3.70/1.00      ( k5_xboole_0(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_4,c_0]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_748,plain,
% 3.70/1.00      ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_740,c_402]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1275,plain,
% 3.70/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = iProver_top ),
% 3.70/1.00      inference(light_normalisation,[status(thm)],[c_1271,c_748]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9,plain,
% 3.70/1.00      ( ~ r1_tarski(X0,X1)
% 3.70/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.70/1.00      | ~ v1_relat_1(X0)
% 3.70/1.00      | ~ v1_relat_1(X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6,plain,
% 3.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_73,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.70/1.00      | ~ r1_tarski(X0,X1)
% 3.70/1.00      | ~ v1_relat_1(X1) ),
% 3.70/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9,c_8,c_6]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_74,plain,
% 3.70/1.00      ( ~ r1_tarski(X0,X1)
% 3.70/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.70/1.00      | ~ v1_relat_1(X1) ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_73]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_394,plain,
% 3.70/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.70/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.70/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2,plain,
% 3.70/1.00      ( ~ r1_tarski(X0,X1)
% 3.70/1.00      | ~ r1_tarski(X0,X2)
% 3.70/1.00      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_400,plain,
% 3.70/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.70/1.00      | r1_tarski(X0,X2) != iProver_top
% 3.70/1.00      | r1_tarski(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_11,negated_conjecture,
% 3.70/1.00      ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_398,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_794,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) != iProver_top
% 3.70/1.00      | r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_400,c_398]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_13,negated_conjecture,
% 3.70/1.00      ( v1_relat_1(sK0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14,plain,
% 3.70/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_16,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_416,plain,
% 3.70/1.00      ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1))
% 3.70/1.00      | ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK0))
% 3.70/1.00      | r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_417,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) != iProver_top
% 3.70/1.00      | r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) != iProver_top
% 3.70/1.00      | r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_513,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(X0))
% 3.70/1.00      | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_74]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_514,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(X0)) = iProver_top
% 3.70/1.00      | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),X0) != iProver_top
% 3.70/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_516,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK0)) = iProver_top
% 3.70/1.00      | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) != iProver_top
% 3.70/1.00      | v1_relat_1(sK0) != iProver_top ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_514]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1,plain,
% 3.70/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_762,plain,
% 3.70/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_763,plain,
% 3.70/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_884,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_794,c_14,c_16,c_417,c_516,c_763]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_888,plain,
% 3.70/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) != iProver_top
% 3.70/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_394,c_884]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12,negated_conjecture,
% 3.70/1.00      ( v1_relat_1(sK1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_15,plain,
% 3.70/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_424,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1))
% 3.70/1.00      | ~ r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1)
% 3.70/1.00      | ~ v1_relat_1(sK1) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_74]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_425,plain,
% 3.70/1.00      ( r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k2_relat_1(sK1)) = iProver_top
% 3.70/1.00      | r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) != iProver_top
% 3.70/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_998,plain,
% 3.70/1.00      ( r1_tarski(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK1) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_888,c_14,c_15,c_16,c_417,c_425,c_516,c_763]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1710,plain,
% 3.70/1.00      ( $false ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1275,c_998]) ).
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  ------                               Statistics
% 3.70/1.00  
% 3.70/1.00  ------ General
% 3.70/1.00  
% 3.70/1.00  abstr_ref_over_cycles:                  0
% 3.70/1.00  abstr_ref_under_cycles:                 0
% 3.70/1.00  gc_basic_clause_elim:                   0
% 3.70/1.00  forced_gc_time:                         0
% 3.70/1.00  parsing_time:                           0.017
% 3.70/1.00  unif_index_cands_time:                  0.
% 3.70/1.00  unif_index_add_time:                    0.
% 3.70/1.00  orderings_time:                         0.
% 3.70/1.00  out_proof_time:                         0.008
% 3.70/1.00  total_time:                             0.396
% 3.70/1.00  num_of_symbols:                         43
% 3.70/1.00  num_of_terms:                           2451
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing
% 3.70/1.00  
% 3.70/1.00  num_of_splits:                          0
% 3.70/1.00  num_of_split_atoms:                     0
% 3.70/1.00  num_of_reused_defs:                     0
% 3.70/1.00  num_eq_ax_congr_red:                    5
% 3.70/1.00  num_of_sem_filtered_clauses:            1
% 3.70/1.00  num_of_subtypes:                        0
% 3.70/1.00  monotx_restored_types:                  0
% 3.70/1.00  sat_num_of_epr_types:                   0
% 3.70/1.00  sat_num_of_non_cyclic_types:            0
% 3.70/1.00  sat_guarded_non_collapsed_types:        0
% 3.70/1.00  num_pure_diseq_elim:                    0
% 3.70/1.00  simp_replaced_by:                       0
% 3.70/1.00  res_preprocessed:                       69
% 3.70/1.00  prep_upred:                             0
% 3.70/1.00  prep_unflattend:                        0
% 3.70/1.00  smt_new_axioms:                         0
% 3.70/1.00  pred_elim_cands:                        2
% 3.70/1.00  pred_elim:                              1
% 3.70/1.00  pred_elim_cl:                           2
% 3.70/1.00  pred_elim_cycles:                       3
% 3.70/1.00  merged_defs:                            2
% 3.70/1.00  merged_defs_ncl:                        0
% 3.70/1.00  bin_hyper_res:                          3
% 3.70/1.00  prep_cycles:                            4
% 3.70/1.00  pred_elim_time:                         0.
% 3.70/1.00  splitting_time:                         0.
% 3.70/1.00  sem_filter_time:                        0.
% 3.70/1.00  monotx_time:                            0.
% 3.70/1.00  subtype_inf_time:                       0.
% 3.70/1.00  
% 3.70/1.00  ------ Problem properties
% 3.70/1.00  
% 3.70/1.00  clauses:                                12
% 3.70/1.00  conjectures:                            3
% 3.70/1.00  epr:                                    3
% 3.70/1.00  horn:                                   12
% 3.70/1.00  ground:                                 3
% 3.70/1.00  unary:                                  8
% 3.70/1.00  binary:                                 0
% 3.70/1.00  lits:                                   20
% 3.70/1.00  lits_eq:                                3
% 3.70/1.00  fd_pure:                                0
% 3.70/1.00  fd_pseudo:                              0
% 3.70/1.00  fd_cond:                                0
% 3.70/1.00  fd_pseudo_cond:                         0
% 3.70/1.00  ac_symbols:                             0
% 3.70/1.00  
% 3.70/1.00  ------ Propositional Solver
% 3.70/1.00  
% 3.70/1.00  prop_solver_calls:                      32
% 3.70/1.00  prop_fast_solver_calls:                 357
% 3.70/1.00  smt_solver_calls:                       0
% 3.70/1.00  smt_fast_solver_calls:                  0
% 3.70/1.00  prop_num_of_clauses:                    801
% 3.70/1.00  prop_preprocess_simplified:             2431
% 3.70/1.00  prop_fo_subsumed:                       4
% 3.70/1.00  prop_solver_time:                       0.
% 3.70/1.00  smt_solver_time:                        0.
% 3.70/1.00  smt_fast_solver_time:                   0.
% 3.70/1.00  prop_fast_solver_time:                  0.
% 3.70/1.00  prop_unsat_core_time:                   0.
% 3.70/1.00  
% 3.70/1.00  ------ QBF
% 3.70/1.00  
% 3.70/1.00  qbf_q_res:                              0
% 3.70/1.00  qbf_num_tautologies:                    0
% 3.70/1.00  qbf_prep_cycles:                        0
% 3.70/1.00  
% 3.70/1.00  ------ BMC1
% 3.70/1.00  
% 3.70/1.00  bmc1_current_bound:                     -1
% 3.70/1.00  bmc1_last_solved_bound:                 -1
% 3.70/1.00  bmc1_unsat_core_size:                   -1
% 3.70/1.00  bmc1_unsat_core_parents_size:           -1
% 3.70/1.00  bmc1_merge_next_fun:                    0
% 3.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation
% 3.70/1.00  
% 3.70/1.00  inst_num_of_clauses:                    217
% 3.70/1.00  inst_num_in_passive:                    67
% 3.70/1.00  inst_num_in_active:                     123
% 3.70/1.00  inst_num_in_unprocessed:                27
% 3.70/1.00  inst_num_of_loops:                      140
% 3.70/1.00  inst_num_of_learning_restarts:          0
% 3.70/1.00  inst_num_moves_active_passive:          12
% 3.70/1.00  inst_lit_activity:                      0
% 3.70/1.00  inst_lit_activity_moves:                0
% 3.70/1.00  inst_num_tautologies:                   0
% 3.70/1.00  inst_num_prop_implied:                  0
% 3.70/1.00  inst_num_existing_simplified:           0
% 3.70/1.00  inst_num_eq_res_simplified:             0
% 3.70/1.00  inst_num_child_elim:                    0
% 3.70/1.00  inst_num_of_dismatching_blockings:      61
% 3.70/1.00  inst_num_of_non_proper_insts:           254
% 3.70/1.00  inst_num_of_duplicates:                 0
% 3.70/1.00  inst_inst_num_from_inst_to_res:         0
% 3.70/1.00  inst_dismatching_checking_time:         0.
% 3.70/1.00  
% 3.70/1.00  ------ Resolution
% 3.70/1.00  
% 3.70/1.00  res_num_of_clauses:                     0
% 3.70/1.00  res_num_in_passive:                     0
% 3.70/1.00  res_num_in_active:                      0
% 3.70/1.00  res_num_of_loops:                       73
% 3.70/1.00  res_forward_subset_subsumed:            51
% 3.70/1.00  res_backward_subset_subsumed:           0
% 3.70/1.00  res_forward_subsumed:                   0
% 3.70/1.00  res_backward_subsumed:                  0
% 3.70/1.00  res_forward_subsumption_resolution:     0
% 3.70/1.00  res_backward_subsumption_resolution:    0
% 3.70/1.00  res_clause_to_clause_subsumption:       191
% 3.70/1.00  res_orphan_elimination:                 0
% 3.70/1.00  res_tautology_del:                      33
% 3.70/1.00  res_num_eq_res_simplified:              0
% 3.70/1.00  res_num_sel_changes:                    0
% 3.70/1.00  res_moves_from_active_to_pass:          0
% 3.70/1.00  
% 3.70/1.00  ------ Superposition
% 3.70/1.00  
% 3.70/1.00  sup_time_total:                         0.
% 3.70/1.00  sup_time_generating:                    0.
% 3.70/1.00  sup_time_sim_full:                      0.
% 3.70/1.00  sup_time_sim_immed:                     0.
% 3.70/1.00  
% 3.70/1.00  sup_num_of_clauses:                     51
% 3.70/1.00  sup_num_in_active:                      27
% 3.70/1.00  sup_num_in_passive:                     24
% 3.70/1.00  sup_num_of_loops:                       26
% 3.70/1.00  sup_fw_superposition:                   62
% 3.70/1.00  sup_bw_superposition:                   26
% 3.70/1.00  sup_immediate_simplified:               19
% 3.70/1.00  sup_given_eliminated:                   0
% 3.70/1.00  comparisons_done:                       0
% 3.70/1.00  comparisons_avoided:                    0
% 3.70/1.00  
% 3.70/1.00  ------ Simplifications
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  sim_fw_subset_subsumed:                 0
% 3.70/1.00  sim_bw_subset_subsumed:                 0
% 3.70/1.00  sim_fw_subsumed:                        2
% 3.70/1.00  sim_bw_subsumed:                        0
% 3.70/1.00  sim_fw_subsumption_res:                 0
% 3.70/1.00  sim_bw_subsumption_res:                 0
% 3.70/1.00  sim_tautology_del:                      0
% 3.70/1.00  sim_eq_tautology_del:                   0
% 3.70/1.00  sim_eq_res_simp:                        0
% 3.70/1.00  sim_fw_demodulated:                     12
% 3.70/1.00  sim_bw_demodulated:                     0
% 3.70/1.00  sim_light_normalised:                   7
% 3.70/1.00  sim_joinable_taut:                      0
% 3.70/1.00  sim_joinable_simp:                      0
% 3.70/1.00  sim_ac_normalised:                      0
% 3.70/1.00  sim_smt_subsumption:                    0
% 3.70/1.00  
%------------------------------------------------------------------------------

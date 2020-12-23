%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:12 EST 2020

% Result     : Theorem 11.74s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 437 expanded)
%              Number of clauses        :   56 (  69 expanded)
%              Number of leaves         :   23 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          :  291 ( 818 expanded)
%              Number of equality atoms :  104 ( 338 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK1))
        & r1_tarski(X0,sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f40,f39])).

fof(f67,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f74])).

fof(f83,plain,(
    ! [X0] :
      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f45,f75])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f75])).

fof(f68,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f50,f75,f76,f76,f75])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f76])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f69,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_653,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_656,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1985,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) = k3_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_653,c_656])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_664,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_663,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1522,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_664,c_663])).

cnf(c_2346,plain,
    ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_1522])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_111,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_12,c_10])).

cnf(c_112,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_651,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_112])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_660,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1969,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X1),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_651,c_660])).

cnf(c_14756,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_1969])).

cnf(c_21,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17317,plain,
    ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14756,c_21])).

cnf(c_17318,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_17317])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_652,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1986,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) = k3_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_652,c_656])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_657,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2532,plain,
    ( r1_tarski(k3_relat_1(sK0),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK0),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_657])).

cnf(c_17337,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) = iProver_top
    | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_17318,c_2532])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_654,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_116,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_12,c_10])).

cnf(c_117,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_116])).

cnf(c_650,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_117])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_659,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1318,plain,
    ( k1_setfam_1(k6_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_659])).

cnf(c_7144,plain,
    ( k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) = k2_relat_1(sK0)
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_1318])).

cnf(c_7645,plain,
    ( k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) = k2_relat_1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7144,c_21])).

cnf(c_8,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_658,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2349,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_relat_1(sK1))))),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_658])).

cnf(c_7660,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k2_relat_1(sK0))),k3_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7645,c_2349])).

cnf(c_5,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_661,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_662,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1410,plain,
    ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_661,c_662])).

cnf(c_7661,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7660,c_1410])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_22,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17337,c_7661,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.74/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/1.98  
% 11.74/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.74/1.98  
% 11.74/1.98  ------  iProver source info
% 11.74/1.98  
% 11.74/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.74/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.74/1.98  git: non_committed_changes: false
% 11.74/1.98  git: last_make_outside_of_git: false
% 11.74/1.98  
% 11.74/1.98  ------ 
% 11.74/1.98  
% 11.74/1.98  ------ Input Options
% 11.74/1.98  
% 11.74/1.98  --out_options                           all
% 11.74/1.98  --tptp_safe_out                         true
% 11.74/1.98  --problem_path                          ""
% 11.74/1.98  --include_path                          ""
% 11.74/1.98  --clausifier                            res/vclausify_rel
% 11.74/1.98  --clausifier_options                    ""
% 11.74/1.98  --stdin                                 false
% 11.74/1.98  --stats_out                             all
% 11.74/1.98  
% 11.74/1.98  ------ General Options
% 11.74/1.98  
% 11.74/1.98  --fof                                   false
% 11.74/1.98  --time_out_real                         305.
% 11.74/1.98  --time_out_virtual                      -1.
% 11.74/1.98  --symbol_type_check                     false
% 11.74/1.98  --clausify_out                          false
% 11.74/1.98  --sig_cnt_out                           false
% 11.74/1.98  --trig_cnt_out                          false
% 11.74/1.98  --trig_cnt_out_tolerance                1.
% 11.74/1.98  --trig_cnt_out_sk_spl                   false
% 11.74/1.98  --abstr_cl_out                          false
% 11.74/1.98  
% 11.74/1.98  ------ Global Options
% 11.74/1.98  
% 11.74/1.98  --schedule                              default
% 11.74/1.98  --add_important_lit                     false
% 11.74/1.98  --prop_solver_per_cl                    1000
% 11.74/1.98  --min_unsat_core                        false
% 11.74/1.98  --soft_assumptions                      false
% 11.74/1.98  --soft_lemma_size                       3
% 11.74/1.98  --prop_impl_unit_size                   0
% 11.74/1.98  --prop_impl_unit                        []
% 11.74/1.98  --share_sel_clauses                     true
% 11.74/1.98  --reset_solvers                         false
% 11.74/1.98  --bc_imp_inh                            [conj_cone]
% 11.74/1.98  --conj_cone_tolerance                   3.
% 11.74/1.98  --extra_neg_conj                        none
% 11.74/1.98  --large_theory_mode                     true
% 11.74/1.98  --prolific_symb_bound                   200
% 11.74/1.98  --lt_threshold                          2000
% 11.74/1.98  --clause_weak_htbl                      true
% 11.74/1.98  --gc_record_bc_elim                     false
% 11.74/1.98  
% 11.74/1.99  ------ Preprocessing Options
% 11.74/1.99  
% 11.74/1.99  --preprocessing_flag                    true
% 11.74/1.99  --time_out_prep_mult                    0.1
% 11.74/1.99  --splitting_mode                        input
% 11.74/1.99  --splitting_grd                         true
% 11.74/1.99  --splitting_cvd                         false
% 11.74/1.99  --splitting_cvd_svl                     false
% 11.74/1.99  --splitting_nvd                         32
% 11.74/1.99  --sub_typing                            true
% 11.74/1.99  --prep_gs_sim                           true
% 11.74/1.99  --prep_unflatten                        true
% 11.74/1.99  --prep_res_sim                          true
% 11.74/1.99  --prep_upred                            true
% 11.74/1.99  --prep_sem_filter                       exhaustive
% 11.74/1.99  --prep_sem_filter_out                   false
% 11.74/1.99  --pred_elim                             true
% 11.74/1.99  --res_sim_input                         true
% 11.74/1.99  --eq_ax_congr_red                       true
% 11.74/1.99  --pure_diseq_elim                       true
% 11.74/1.99  --brand_transform                       false
% 11.74/1.99  --non_eq_to_eq                          false
% 11.74/1.99  --prep_def_merge                        true
% 11.74/1.99  --prep_def_merge_prop_impl              false
% 11.74/1.99  --prep_def_merge_mbd                    true
% 11.74/1.99  --prep_def_merge_tr_red                 false
% 11.74/1.99  --prep_def_merge_tr_cl                  false
% 11.74/1.99  --smt_preprocessing                     true
% 11.74/1.99  --smt_ac_axioms                         fast
% 11.74/1.99  --preprocessed_out                      false
% 11.74/1.99  --preprocessed_stats                    false
% 11.74/1.99  
% 11.74/1.99  ------ Abstraction refinement Options
% 11.74/1.99  
% 11.74/1.99  --abstr_ref                             []
% 11.74/1.99  --abstr_ref_prep                        false
% 11.74/1.99  --abstr_ref_until_sat                   false
% 11.74/1.99  --abstr_ref_sig_restrict                funpre
% 11.74/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.74/1.99  --abstr_ref_under                       []
% 11.74/1.99  
% 11.74/1.99  ------ SAT Options
% 11.74/1.99  
% 11.74/1.99  --sat_mode                              false
% 11.74/1.99  --sat_fm_restart_options                ""
% 11.74/1.99  --sat_gr_def                            false
% 11.74/1.99  --sat_epr_types                         true
% 11.74/1.99  --sat_non_cyclic_types                  false
% 11.74/1.99  --sat_finite_models                     false
% 11.74/1.99  --sat_fm_lemmas                         false
% 11.74/1.99  --sat_fm_prep                           false
% 11.74/1.99  --sat_fm_uc_incr                        true
% 11.74/1.99  --sat_out_model                         small
% 11.74/1.99  --sat_out_clauses                       false
% 11.74/1.99  
% 11.74/1.99  ------ QBF Options
% 11.74/1.99  
% 11.74/1.99  --qbf_mode                              false
% 11.74/1.99  --qbf_elim_univ                         false
% 11.74/1.99  --qbf_dom_inst                          none
% 11.74/1.99  --qbf_dom_pre_inst                      false
% 11.74/1.99  --qbf_sk_in                             false
% 11.74/1.99  --qbf_pred_elim                         true
% 11.74/1.99  --qbf_split                             512
% 11.74/1.99  
% 11.74/1.99  ------ BMC1 Options
% 11.74/1.99  
% 11.74/1.99  --bmc1_incremental                      false
% 11.74/1.99  --bmc1_axioms                           reachable_all
% 11.74/1.99  --bmc1_min_bound                        0
% 11.74/1.99  --bmc1_max_bound                        -1
% 11.74/1.99  --bmc1_max_bound_default                -1
% 11.74/1.99  --bmc1_symbol_reachability              true
% 11.74/1.99  --bmc1_property_lemmas                  false
% 11.74/1.99  --bmc1_k_induction                      false
% 11.74/1.99  --bmc1_non_equiv_states                 false
% 11.74/1.99  --bmc1_deadlock                         false
% 11.74/1.99  --bmc1_ucm                              false
% 11.74/1.99  --bmc1_add_unsat_core                   none
% 11.74/1.99  --bmc1_unsat_core_children              false
% 11.74/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.74/1.99  --bmc1_out_stat                         full
% 11.74/1.99  --bmc1_ground_init                      false
% 11.74/1.99  --bmc1_pre_inst_next_state              false
% 11.74/1.99  --bmc1_pre_inst_state                   false
% 11.74/1.99  --bmc1_pre_inst_reach_state             false
% 11.74/1.99  --bmc1_out_unsat_core                   false
% 11.74/1.99  --bmc1_aig_witness_out                  false
% 11.74/1.99  --bmc1_verbose                          false
% 11.74/1.99  --bmc1_dump_clauses_tptp                false
% 11.74/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.74/1.99  --bmc1_dump_file                        -
% 11.74/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.74/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.74/1.99  --bmc1_ucm_extend_mode                  1
% 11.74/1.99  --bmc1_ucm_init_mode                    2
% 11.74/1.99  --bmc1_ucm_cone_mode                    none
% 11.74/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.74/1.99  --bmc1_ucm_relax_model                  4
% 11.74/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.74/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.74/1.99  --bmc1_ucm_layered_model                none
% 11.74/1.99  --bmc1_ucm_max_lemma_size               10
% 11.74/1.99  
% 11.74/1.99  ------ AIG Options
% 11.74/1.99  
% 11.74/1.99  --aig_mode                              false
% 11.74/1.99  
% 11.74/1.99  ------ Instantiation Options
% 11.74/1.99  
% 11.74/1.99  --instantiation_flag                    true
% 11.74/1.99  --inst_sos_flag                         true
% 11.74/1.99  --inst_sos_phase                        true
% 11.74/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.74/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.74/1.99  --inst_lit_sel_side                     num_symb
% 11.74/1.99  --inst_solver_per_active                1400
% 11.74/1.99  --inst_solver_calls_frac                1.
% 11.74/1.99  --inst_passive_queue_type               priority_queues
% 11.74/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.74/1.99  --inst_passive_queues_freq              [25;2]
% 11.74/1.99  --inst_dismatching                      true
% 11.74/1.99  --inst_eager_unprocessed_to_passive     true
% 11.74/1.99  --inst_prop_sim_given                   true
% 11.74/1.99  --inst_prop_sim_new                     false
% 11.74/1.99  --inst_subs_new                         false
% 11.74/1.99  --inst_eq_res_simp                      false
% 11.74/1.99  --inst_subs_given                       false
% 11.74/1.99  --inst_orphan_elimination               true
% 11.74/1.99  --inst_learning_loop_flag               true
% 11.74/1.99  --inst_learning_start                   3000
% 11.74/1.99  --inst_learning_factor                  2
% 11.74/1.99  --inst_start_prop_sim_after_learn       3
% 11.74/1.99  --inst_sel_renew                        solver
% 11.74/1.99  --inst_lit_activity_flag                true
% 11.74/1.99  --inst_restr_to_given                   false
% 11.74/1.99  --inst_activity_threshold               500
% 11.74/1.99  --inst_out_proof                        true
% 11.74/1.99  
% 11.74/1.99  ------ Resolution Options
% 11.74/1.99  
% 11.74/1.99  --resolution_flag                       true
% 11.74/1.99  --res_lit_sel                           adaptive
% 11.74/1.99  --res_lit_sel_side                      none
% 11.74/1.99  --res_ordering                          kbo
% 11.74/1.99  --res_to_prop_solver                    active
% 11.74/1.99  --res_prop_simpl_new                    false
% 11.74/1.99  --res_prop_simpl_given                  true
% 11.74/1.99  --res_passive_queue_type                priority_queues
% 11.74/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.74/1.99  --res_passive_queues_freq               [15;5]
% 11.74/1.99  --res_forward_subs                      full
% 11.74/1.99  --res_backward_subs                     full
% 11.74/1.99  --res_forward_subs_resolution           true
% 11.74/1.99  --res_backward_subs_resolution          true
% 11.74/1.99  --res_orphan_elimination                true
% 11.74/1.99  --res_time_limit                        2.
% 11.74/1.99  --res_out_proof                         true
% 11.74/1.99  
% 11.74/1.99  ------ Superposition Options
% 11.74/1.99  
% 11.74/1.99  --superposition_flag                    true
% 11.74/1.99  --sup_passive_queue_type                priority_queues
% 11.74/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.74/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.74/1.99  --demod_completeness_check              fast
% 11.74/1.99  --demod_use_ground                      true
% 11.74/1.99  --sup_to_prop_solver                    passive
% 11.74/1.99  --sup_prop_simpl_new                    true
% 11.74/1.99  --sup_prop_simpl_given                  true
% 11.74/1.99  --sup_fun_splitting                     true
% 11.74/1.99  --sup_smt_interval                      50000
% 11.74/1.99  
% 11.74/1.99  ------ Superposition Simplification Setup
% 11.74/1.99  
% 11.74/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.74/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.74/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.74/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.74/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.74/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.74/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.74/1.99  --sup_immed_triv                        [TrivRules]
% 11.74/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/1.99  --sup_immed_bw_main                     []
% 11.74/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.74/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.74/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/1.99  --sup_input_bw                          []
% 11.74/1.99  
% 11.74/1.99  ------ Combination Options
% 11.74/1.99  
% 11.74/1.99  --comb_res_mult                         3
% 11.74/1.99  --comb_sup_mult                         2
% 11.74/1.99  --comb_inst_mult                        10
% 11.74/1.99  
% 11.74/1.99  ------ Debug Options
% 11.74/1.99  
% 11.74/1.99  --dbg_backtrace                         false
% 11.74/1.99  --dbg_dump_prop_clauses                 false
% 11.74/1.99  --dbg_dump_prop_clauses_file            -
% 11.74/1.99  --dbg_out_stat                          false
% 11.74/1.99  ------ Parsing...
% 11.74/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.74/1.99  
% 11.74/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.74/1.99  
% 11.74/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.74/1.99  
% 11.74/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.74/1.99  ------ Proving...
% 11.74/1.99  ------ Problem Properties 
% 11.74/1.99  
% 11.74/1.99  
% 11.74/1.99  clauses                                 17
% 11.74/1.99  conjectures                             4
% 11.74/1.99  EPR                                     7
% 11.74/1.99  Horn                                    17
% 11.74/1.99  unary                                   7
% 11.74/1.99  binary                                  4
% 11.74/1.99  lits                                    33
% 11.74/1.99  lits eq                                 4
% 11.74/1.99  fd_pure                                 0
% 11.74/1.99  fd_pseudo                               0
% 11.74/1.99  fd_cond                                 0
% 11.74/1.99  fd_pseudo_cond                          1
% 11.74/1.99  AC symbols                              0
% 11.74/1.99  
% 11.74/1.99  ------ Schedule dynamic 5 is on 
% 11.74/1.99  
% 11.74/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.74/1.99  
% 11.74/1.99  
% 11.74/1.99  ------ 
% 11.74/1.99  Current options:
% 11.74/1.99  ------ 
% 11.74/1.99  
% 11.74/1.99  ------ Input Options
% 11.74/1.99  
% 11.74/1.99  --out_options                           all
% 11.74/1.99  --tptp_safe_out                         true
% 11.74/1.99  --problem_path                          ""
% 11.74/1.99  --include_path                          ""
% 11.74/1.99  --clausifier                            res/vclausify_rel
% 11.74/1.99  --clausifier_options                    ""
% 11.74/1.99  --stdin                                 false
% 11.74/1.99  --stats_out                             all
% 11.74/1.99  
% 11.74/1.99  ------ General Options
% 11.74/1.99  
% 11.74/1.99  --fof                                   false
% 11.74/1.99  --time_out_real                         305.
% 11.74/1.99  --time_out_virtual                      -1.
% 11.74/1.99  --symbol_type_check                     false
% 11.74/1.99  --clausify_out                          false
% 11.74/1.99  --sig_cnt_out                           false
% 11.74/1.99  --trig_cnt_out                          false
% 11.74/1.99  --trig_cnt_out_tolerance                1.
% 11.74/1.99  --trig_cnt_out_sk_spl                   false
% 11.74/1.99  --abstr_cl_out                          false
% 11.74/1.99  
% 11.74/1.99  ------ Global Options
% 11.74/1.99  
% 11.74/1.99  --schedule                              default
% 11.74/1.99  --add_important_lit                     false
% 11.74/1.99  --prop_solver_per_cl                    1000
% 11.74/1.99  --min_unsat_core                        false
% 11.74/1.99  --soft_assumptions                      false
% 11.74/1.99  --soft_lemma_size                       3
% 11.74/1.99  --prop_impl_unit_size                   0
% 11.74/1.99  --prop_impl_unit                        []
% 11.74/1.99  --share_sel_clauses                     true
% 11.74/1.99  --reset_solvers                         false
% 11.74/1.99  --bc_imp_inh                            [conj_cone]
% 11.74/1.99  --conj_cone_tolerance                   3.
% 11.74/1.99  --extra_neg_conj                        none
% 11.74/1.99  --large_theory_mode                     true
% 11.74/1.99  --prolific_symb_bound                   200
% 11.74/1.99  --lt_threshold                          2000
% 11.74/1.99  --clause_weak_htbl                      true
% 11.74/1.99  --gc_record_bc_elim                     false
% 11.74/1.99  
% 11.74/1.99  ------ Preprocessing Options
% 11.74/1.99  
% 11.74/1.99  --preprocessing_flag                    true
% 11.74/1.99  --time_out_prep_mult                    0.1
% 11.74/1.99  --splitting_mode                        input
% 11.74/1.99  --splitting_grd                         true
% 11.74/1.99  --splitting_cvd                         false
% 11.74/1.99  --splitting_cvd_svl                     false
% 11.74/1.99  --splitting_nvd                         32
% 11.74/1.99  --sub_typing                            true
% 11.74/1.99  --prep_gs_sim                           true
% 11.74/1.99  --prep_unflatten                        true
% 11.74/1.99  --prep_res_sim                          true
% 11.74/1.99  --prep_upred                            true
% 11.74/1.99  --prep_sem_filter                       exhaustive
% 11.74/1.99  --prep_sem_filter_out                   false
% 11.74/1.99  --pred_elim                             true
% 11.74/1.99  --res_sim_input                         true
% 11.74/1.99  --eq_ax_congr_red                       true
% 11.74/1.99  --pure_diseq_elim                       true
% 11.74/1.99  --brand_transform                       false
% 11.74/1.99  --non_eq_to_eq                          false
% 11.74/1.99  --prep_def_merge                        true
% 11.74/1.99  --prep_def_merge_prop_impl              false
% 11.74/1.99  --prep_def_merge_mbd                    true
% 11.74/1.99  --prep_def_merge_tr_red                 false
% 11.74/1.99  --prep_def_merge_tr_cl                  false
% 11.74/1.99  --smt_preprocessing                     true
% 11.74/1.99  --smt_ac_axioms                         fast
% 11.74/1.99  --preprocessed_out                      false
% 11.74/1.99  --preprocessed_stats                    false
% 11.74/1.99  
% 11.74/1.99  ------ Abstraction refinement Options
% 11.74/1.99  
% 11.74/1.99  --abstr_ref                             []
% 11.74/1.99  --abstr_ref_prep                        false
% 11.74/1.99  --abstr_ref_until_sat                   false
% 11.74/1.99  --abstr_ref_sig_restrict                funpre
% 11.74/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.74/1.99  --abstr_ref_under                       []
% 11.74/1.99  
% 11.74/1.99  ------ SAT Options
% 11.74/1.99  
% 11.74/1.99  --sat_mode                              false
% 11.74/1.99  --sat_fm_restart_options                ""
% 11.74/1.99  --sat_gr_def                            false
% 11.74/1.99  --sat_epr_types                         true
% 11.74/1.99  --sat_non_cyclic_types                  false
% 11.74/1.99  --sat_finite_models                     false
% 11.74/1.99  --sat_fm_lemmas                         false
% 11.74/1.99  --sat_fm_prep                           false
% 11.74/1.99  --sat_fm_uc_incr                        true
% 11.74/1.99  --sat_out_model                         small
% 11.74/1.99  --sat_out_clauses                       false
% 11.74/1.99  
% 11.74/1.99  ------ QBF Options
% 11.74/1.99  
% 11.74/1.99  --qbf_mode                              false
% 11.74/1.99  --qbf_elim_univ                         false
% 11.74/1.99  --qbf_dom_inst                          none
% 11.74/1.99  --qbf_dom_pre_inst                      false
% 11.74/1.99  --qbf_sk_in                             false
% 11.74/1.99  --qbf_pred_elim                         true
% 11.74/1.99  --qbf_split                             512
% 11.74/1.99  
% 11.74/1.99  ------ BMC1 Options
% 11.74/1.99  
% 11.74/1.99  --bmc1_incremental                      false
% 11.74/1.99  --bmc1_axioms                           reachable_all
% 11.74/1.99  --bmc1_min_bound                        0
% 11.74/1.99  --bmc1_max_bound                        -1
% 11.74/1.99  --bmc1_max_bound_default                -1
% 11.74/1.99  --bmc1_symbol_reachability              true
% 11.74/1.99  --bmc1_property_lemmas                  false
% 11.74/1.99  --bmc1_k_induction                      false
% 11.74/1.99  --bmc1_non_equiv_states                 false
% 11.74/1.99  --bmc1_deadlock                         false
% 11.74/1.99  --bmc1_ucm                              false
% 11.74/1.99  --bmc1_add_unsat_core                   none
% 11.74/1.99  --bmc1_unsat_core_children              false
% 11.74/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.74/1.99  --bmc1_out_stat                         full
% 11.74/1.99  --bmc1_ground_init                      false
% 11.74/1.99  --bmc1_pre_inst_next_state              false
% 11.74/1.99  --bmc1_pre_inst_state                   false
% 11.74/1.99  --bmc1_pre_inst_reach_state             false
% 11.74/1.99  --bmc1_out_unsat_core                   false
% 11.74/1.99  --bmc1_aig_witness_out                  false
% 11.74/1.99  --bmc1_verbose                          false
% 11.74/1.99  --bmc1_dump_clauses_tptp                false
% 11.74/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.74/1.99  --bmc1_dump_file                        -
% 11.74/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.74/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.74/1.99  --bmc1_ucm_extend_mode                  1
% 11.74/1.99  --bmc1_ucm_init_mode                    2
% 11.74/1.99  --bmc1_ucm_cone_mode                    none
% 11.74/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.74/1.99  --bmc1_ucm_relax_model                  4
% 11.74/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.74/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.74/1.99  --bmc1_ucm_layered_model                none
% 11.74/1.99  --bmc1_ucm_max_lemma_size               10
% 11.74/1.99  
% 11.74/1.99  ------ AIG Options
% 11.74/1.99  
% 11.74/1.99  --aig_mode                              false
% 11.74/1.99  
% 11.74/1.99  ------ Instantiation Options
% 11.74/1.99  
% 11.74/1.99  --instantiation_flag                    true
% 11.74/1.99  --inst_sos_flag                         true
% 11.74/1.99  --inst_sos_phase                        true
% 11.74/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.74/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.74/1.99  --inst_lit_sel_side                     none
% 11.74/1.99  --inst_solver_per_active                1400
% 11.74/1.99  --inst_solver_calls_frac                1.
% 11.74/1.99  --inst_passive_queue_type               priority_queues
% 11.74/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.74/1.99  --inst_passive_queues_freq              [25;2]
% 11.74/1.99  --inst_dismatching                      true
% 11.74/1.99  --inst_eager_unprocessed_to_passive     true
% 11.74/1.99  --inst_prop_sim_given                   true
% 11.74/1.99  --inst_prop_sim_new                     false
% 11.74/1.99  --inst_subs_new                         false
% 11.74/1.99  --inst_eq_res_simp                      false
% 11.74/1.99  --inst_subs_given                       false
% 11.74/1.99  --inst_orphan_elimination               true
% 11.74/1.99  --inst_learning_loop_flag               true
% 11.74/1.99  --inst_learning_start                   3000
% 11.74/1.99  --inst_learning_factor                  2
% 11.74/1.99  --inst_start_prop_sim_after_learn       3
% 11.74/1.99  --inst_sel_renew                        solver
% 11.74/1.99  --inst_lit_activity_flag                true
% 11.74/1.99  --inst_restr_to_given                   false
% 11.74/1.99  --inst_activity_threshold               500
% 11.74/1.99  --inst_out_proof                        true
% 11.74/1.99  
% 11.74/1.99  ------ Resolution Options
% 11.74/1.99  
% 11.74/1.99  --resolution_flag                       false
% 11.74/1.99  --res_lit_sel                           adaptive
% 11.74/1.99  --res_lit_sel_side                      none
% 11.74/1.99  --res_ordering                          kbo
% 11.74/1.99  --res_to_prop_solver                    active
% 11.74/1.99  --res_prop_simpl_new                    false
% 11.74/1.99  --res_prop_simpl_given                  true
% 11.74/1.99  --res_passive_queue_type                priority_queues
% 11.74/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.74/1.99  --res_passive_queues_freq               [15;5]
% 11.74/1.99  --res_forward_subs                      full
% 11.74/1.99  --res_backward_subs                     full
% 11.74/1.99  --res_forward_subs_resolution           true
% 11.74/1.99  --res_backward_subs_resolution          true
% 11.74/1.99  --res_orphan_elimination                true
% 11.74/1.99  --res_time_limit                        2.
% 11.74/1.99  --res_out_proof                         true
% 11.74/1.99  
% 11.74/1.99  ------ Superposition Options
% 11.74/1.99  
% 11.74/1.99  --superposition_flag                    true
% 11.74/1.99  --sup_passive_queue_type                priority_queues
% 11.74/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.74/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.74/1.99  --demod_completeness_check              fast
% 11.74/1.99  --demod_use_ground                      true
% 11.74/1.99  --sup_to_prop_solver                    passive
% 11.74/1.99  --sup_prop_simpl_new                    true
% 11.74/1.99  --sup_prop_simpl_given                  true
% 11.74/1.99  --sup_fun_splitting                     true
% 11.74/1.99  --sup_smt_interval                      50000
% 11.74/1.99  
% 11.74/1.99  ------ Superposition Simplification Setup
% 11.74/1.99  
% 11.74/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.74/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.74/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.74/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.74/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.74/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.74/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.74/1.99  --sup_immed_triv                        [TrivRules]
% 11.74/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/1.99  --sup_immed_bw_main                     []
% 11.74/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.74/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.74/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/1.99  --sup_input_bw                          []
% 11.74/1.99  
% 11.74/1.99  ------ Combination Options
% 11.74/1.99  
% 11.74/1.99  --comb_res_mult                         3
% 11.74/1.99  --comb_sup_mult                         2
% 11.74/1.99  --comb_inst_mult                        10
% 11.74/1.99  
% 11.74/1.99  ------ Debug Options
% 11.74/1.99  
% 11.74/1.99  --dbg_backtrace                         false
% 11.74/1.99  --dbg_dump_prop_clauses                 false
% 11.74/1.99  --dbg_dump_prop_clauses_file            -
% 11.74/1.99  --dbg_out_stat                          false
% 11.74/1.99  
% 11.74/1.99  
% 11.74/1.99  
% 11.74/1.99  
% 11.74/1.99  ------ Proving...
% 11.74/1.99  
% 11.74/1.99  
% 11.74/1.99  % SZS status Theorem for theBenchmark.p
% 11.74/1.99  
% 11.74/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.74/1.99  
% 11.74/1.99  fof(f21,conjecture,(
% 11.74/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f22,negated_conjecture,(
% 11.74/1.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 11.74/1.99    inference(negated_conjecture,[],[f21])).
% 11.74/1.99  
% 11.74/1.99  fof(f34,plain,(
% 11.74/1.99    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 11.74/1.99    inference(ennf_transformation,[],[f22])).
% 11.74/1.99  
% 11.74/1.99  fof(f35,plain,(
% 11.74/1.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 11.74/1.99    inference(flattening,[],[f34])).
% 11.74/1.99  
% 11.74/1.99  fof(f40,plain,(
% 11.74/1.99    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK1)) & r1_tarski(X0,sK1) & v1_relat_1(sK1))) )),
% 11.74/1.99    introduced(choice_axiom,[])).
% 11.74/1.99  
% 11.74/1.99  fof(f39,plain,(
% 11.74/1.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 11.74/1.99    introduced(choice_axiom,[])).
% 11.74/1.99  
% 11.74/1.99  fof(f41,plain,(
% 11.74/1.99    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 11.74/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f40,f39])).
% 11.74/1.99  
% 11.74/1.99  fof(f67,plain,(
% 11.74/1.99    v1_relat_1(sK1)),
% 11.74/1.99    inference(cnf_transformation,[],[f41])).
% 11.74/1.99  
% 11.74/1.99  fof(f19,axiom,(
% 11.74/1.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f31,plain,(
% 11.74/1.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 11.74/1.99    inference(ennf_transformation,[],[f19])).
% 11.74/1.99  
% 11.74/1.99  fof(f63,plain,(
% 11.74/1.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f31])).
% 11.74/1.99  
% 11.74/1.99  fof(f15,axiom,(
% 11.74/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f58,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.74/1.99    inference(cnf_transformation,[],[f15])).
% 11.74/1.99  
% 11.74/1.99  fof(f9,axiom,(
% 11.74/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f52,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f9])).
% 11.74/1.99  
% 11.74/1.99  fof(f10,axiom,(
% 11.74/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f53,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f10])).
% 11.74/1.99  
% 11.74/1.99  fof(f11,axiom,(
% 11.74/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f54,plain,(
% 11.74/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f11])).
% 11.74/1.99  
% 11.74/1.99  fof(f12,axiom,(
% 11.74/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f55,plain,(
% 11.74/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f12])).
% 11.74/1.99  
% 11.74/1.99  fof(f13,axiom,(
% 11.74/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f56,plain,(
% 11.74/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f13])).
% 11.74/1.99  
% 11.74/1.99  fof(f14,axiom,(
% 11.74/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f57,plain,(
% 11.74/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f14])).
% 11.74/1.99  
% 11.74/1.99  fof(f70,plain,(
% 11.74/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f56,f57])).
% 11.74/1.99  
% 11.74/1.99  fof(f71,plain,(
% 11.74/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f55,f70])).
% 11.74/1.99  
% 11.74/1.99  fof(f72,plain,(
% 11.74/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f54,f71])).
% 11.74/1.99  
% 11.74/1.99  fof(f73,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f53,f72])).
% 11.74/1.99  
% 11.74/1.99  fof(f74,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f52,f73])).
% 11.74/1.99  
% 11.74/1.99  fof(f75,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.74/1.99    inference(definition_unfolding,[],[f58,f74])).
% 11.74/1.99  
% 11.74/1.99  fof(f83,plain,(
% 11.74/1.99    ( ! [X0] : (k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f63,f75])).
% 11.74/1.99  
% 11.74/1.99  fof(f1,axiom,(
% 11.74/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f36,plain,(
% 11.74/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.74/1.99    inference(nnf_transformation,[],[f1])).
% 11.74/1.99  
% 11.74/1.99  fof(f37,plain,(
% 11.74/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.74/1.99    inference(flattening,[],[f36])).
% 11.74/1.99  
% 11.74/1.99  fof(f43,plain,(
% 11.74/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.74/1.99    inference(cnf_transformation,[],[f37])).
% 11.74/1.99  
% 11.74/1.99  fof(f84,plain,(
% 11.74/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.74/1.99    inference(equality_resolution,[],[f43])).
% 11.74/1.99  
% 11.74/1.99  fof(f2,axiom,(
% 11.74/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f23,plain,(
% 11.74/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.74/1.99    inference(ennf_transformation,[],[f2])).
% 11.74/1.99  
% 11.74/1.99  fof(f45,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f23])).
% 11.74/1.99  
% 11.74/1.99  fof(f77,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f45,f75])).
% 11.74/1.99  
% 11.74/1.99  fof(f20,axiom,(
% 11.74/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f32,plain,(
% 11.74/1.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.74/1.99    inference(ennf_transformation,[],[f20])).
% 11.74/1.99  
% 11.74/1.99  fof(f33,plain,(
% 11.74/1.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.74/1.99    inference(flattening,[],[f32])).
% 11.74/1.99  
% 11.74/1.99  fof(f64,plain,(
% 11.74/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f33])).
% 11.74/1.99  
% 11.74/1.99  fof(f18,axiom,(
% 11.74/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f30,plain,(
% 11.74/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.74/1.99    inference(ennf_transformation,[],[f18])).
% 11.74/1.99  
% 11.74/1.99  fof(f62,plain,(
% 11.74/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f30])).
% 11.74/1.99  
% 11.74/1.99  fof(f17,axiom,(
% 11.74/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f38,plain,(
% 11.74/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.74/1.99    inference(nnf_transformation,[],[f17])).
% 11.74/1.99  
% 11.74/1.99  fof(f61,plain,(
% 11.74/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f38])).
% 11.74/1.99  
% 11.74/1.99  fof(f5,axiom,(
% 11.74/1.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f25,plain,(
% 11.74/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.74/1.99    inference(ennf_transformation,[],[f5])).
% 11.74/1.99  
% 11.74/1.99  fof(f26,plain,(
% 11.74/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.74/1.99    inference(flattening,[],[f25])).
% 11.74/1.99  
% 11.74/1.99  fof(f48,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f26])).
% 11.74/1.99  
% 11.74/1.99  fof(f66,plain,(
% 11.74/1.99    v1_relat_1(sK0)),
% 11.74/1.99    inference(cnf_transformation,[],[f41])).
% 11.74/1.99  
% 11.74/1.99  fof(f8,axiom,(
% 11.74/1.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f28,plain,(
% 11.74/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.74/1.99    inference(ennf_transformation,[],[f8])).
% 11.74/1.99  
% 11.74/1.99  fof(f29,plain,(
% 11.74/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.74/1.99    inference(flattening,[],[f28])).
% 11.74/1.99  
% 11.74/1.99  fof(f51,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f29])).
% 11.74/1.99  
% 11.74/1.99  fof(f82,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f51,f75])).
% 11.74/1.99  
% 11.74/1.99  fof(f68,plain,(
% 11.74/1.99    r1_tarski(sK0,sK1)),
% 11.74/1.99    inference(cnf_transformation,[],[f41])).
% 11.74/1.99  
% 11.74/1.99  fof(f65,plain,(
% 11.74/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f33])).
% 11.74/1.99  
% 11.74/1.99  fof(f6,axiom,(
% 11.74/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f27,plain,(
% 11.74/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.74/1.99    inference(ennf_transformation,[],[f6])).
% 11.74/1.99  
% 11.74/1.99  fof(f49,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f27])).
% 11.74/1.99  
% 11.74/1.99  fof(f16,axiom,(
% 11.74/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f59,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.74/1.99    inference(cnf_transformation,[],[f16])).
% 11.74/1.99  
% 11.74/1.99  fof(f76,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.74/1.99    inference(definition_unfolding,[],[f59,f74])).
% 11.74/1.99  
% 11.74/1.99  fof(f80,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f49,f76])).
% 11.74/1.99  
% 11.74/1.99  fof(f7,axiom,(
% 11.74/1.99    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f50,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 11.74/1.99    inference(cnf_transformation,[],[f7])).
% 11.74/1.99  
% 11.74/1.99  fof(f81,plain,(
% 11.74/1.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 11.74/1.99    inference(definition_unfolding,[],[f50,f75,f76,f76,f75])).
% 11.74/1.99  
% 11.74/1.99  fof(f4,axiom,(
% 11.74/1.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f47,plain,(
% 11.74/1.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f4])).
% 11.74/1.99  
% 11.74/1.99  fof(f79,plain,(
% 11.74/1.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f47,f76])).
% 11.74/1.99  
% 11.74/1.99  fof(f3,axiom,(
% 11.74/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.74/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.99  
% 11.74/1.99  fof(f24,plain,(
% 11.74/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.74/1.99    inference(ennf_transformation,[],[f3])).
% 11.74/1.99  
% 11.74/1.99  fof(f46,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.74/1.99    inference(cnf_transformation,[],[f24])).
% 11.74/1.99  
% 11.74/1.99  fof(f78,plain,(
% 11.74/1.99    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 11.74/1.99    inference(definition_unfolding,[],[f46,f75])).
% 11.74/1.99  
% 11.74/1.99  fof(f69,plain,(
% 11.74/1.99    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 11.74/1.99    inference(cnf_transformation,[],[f41])).
% 11.74/1.99  
% 11.74/1.99  cnf(c_18,negated_conjecture,
% 11.74/1.99      ( v1_relat_1(sK1) ),
% 11.74/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_653,plain,
% 11.74/1.99      ( v1_relat_1(sK1) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_13,plain,
% 11.74/1.99      ( ~ v1_relat_1(X0)
% 11.74/1.99      | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 11.74/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_656,plain,
% 11.74/1.99      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 11.74/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_1985,plain,
% 11.74/1.99      ( k3_tarski(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) = k3_relat_1(sK1) ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_653,c_656]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_1,plain,
% 11.74/1.99      ( r1_tarski(X0,X0) ),
% 11.74/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_664,plain,
% 11.74/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_3,plain,
% 11.74/1.99      ( r1_tarski(X0,X1)
% 11.74/1.99      | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 11.74/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_663,plain,
% 11.74/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.74/1.99      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) != iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_1522,plain,
% 11.74/1.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_664,c_663]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_2346,plain,
% 11.74/1.99      ( r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) = iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_1985,c_1522]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_15,plain,
% 11.74/1.99      ( ~ r1_tarski(X0,X1)
% 11.74/1.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.74/1.99      | ~ v1_relat_1(X0)
% 11.74/1.99      | ~ v1_relat_1(X1) ),
% 11.74/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_12,plain,
% 11.74/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.74/1.99      | ~ v1_relat_1(X1)
% 11.74/1.99      | v1_relat_1(X0) ),
% 11.74/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_10,plain,
% 11.74/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.74/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_111,plain,
% 11.74/1.99      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.74/1.99      | ~ r1_tarski(X0,X1)
% 11.74/1.99      | ~ v1_relat_1(X1) ),
% 11.74/1.99      inference(global_propositional_subsumption,
% 11.74/1.99                [status(thm)],
% 11.74/1.99                [c_15,c_12,c_10]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_112,plain,
% 11.74/1.99      ( ~ r1_tarski(X0,X1)
% 11.74/1.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 11.74/1.99      | ~ v1_relat_1(X1) ),
% 11.74/1.99      inference(renaming,[status(thm)],[c_111]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_651,plain,
% 11.74/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.74/1.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 11.74/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_112]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_6,plain,
% 11.74/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.74/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_660,plain,
% 11.74/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.74/1.99      | r1_tarski(X1,X2) != iProver_top
% 11.74/1.99      | r1_tarski(X0,X2) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_1969,plain,
% 11.74/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.74/1.99      | r1_tarski(k1_relat_1(X1),X2) != iProver_top
% 11.74/1.99      | r1_tarski(k1_relat_1(X0),X2) = iProver_top
% 11.74/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_651,c_660]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_14756,plain,
% 11.74/1.99      ( r1_tarski(X0,sK1) != iProver_top
% 11.74/1.99      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top
% 11.74/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_2346,c_1969]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_21,plain,
% 11.74/1.99      ( v1_relat_1(sK1) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_17317,plain,
% 11.74/1.99      ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top
% 11.74/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.74/1.99      inference(global_propositional_subsumption,
% 11.74/1.99                [status(thm)],
% 11.74/1.99                [c_14756,c_21]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_17318,plain,
% 11.74/1.99      ( r1_tarski(X0,sK1) != iProver_top
% 11.74/1.99      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) = iProver_top ),
% 11.74/1.99      inference(renaming,[status(thm)],[c_17317]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_19,negated_conjecture,
% 11.74/1.99      ( v1_relat_1(sK0) ),
% 11.74/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_652,plain,
% 11.74/1.99      ( v1_relat_1(sK0) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_1986,plain,
% 11.74/1.99      ( k3_tarski(k6_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) = k3_relat_1(sK0) ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_652,c_656]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_9,plain,
% 11.74/1.99      ( ~ r1_tarski(X0,X1)
% 11.74/1.99      | ~ r1_tarski(X2,X1)
% 11.74/1.99      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 11.74/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_657,plain,
% 11.74/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.74/1.99      | r1_tarski(X2,X1) != iProver_top
% 11.74/1.99      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_2532,plain,
% 11.74/1.99      ( r1_tarski(k3_relat_1(sK0),X0) = iProver_top
% 11.74/1.99      | r1_tarski(k2_relat_1(sK0),X0) != iProver_top
% 11.74/1.99      | r1_tarski(k1_relat_1(sK0),X0) != iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_1986,c_657]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_17337,plain,
% 11.74/1.99      ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) = iProver_top
% 11.74/1.99      | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) != iProver_top
% 11.74/1.99      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_17318,c_2532]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_17,negated_conjecture,
% 11.74/1.99      ( r1_tarski(sK0,sK1) ),
% 11.74/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_654,plain,
% 11.74/1.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_14,plain,
% 11.74/1.99      ( ~ r1_tarski(X0,X1)
% 11.74/1.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.74/1.99      | ~ v1_relat_1(X0)
% 11.74/1.99      | ~ v1_relat_1(X1) ),
% 11.74/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_116,plain,
% 11.74/1.99      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.74/1.99      | ~ r1_tarski(X0,X1)
% 11.74/1.99      | ~ v1_relat_1(X1) ),
% 11.74/1.99      inference(global_propositional_subsumption,
% 11.74/1.99                [status(thm)],
% 11.74/1.99                [c_14,c_12,c_10]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_117,plain,
% 11.74/1.99      ( ~ r1_tarski(X0,X1)
% 11.74/1.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 11.74/1.99      | ~ v1_relat_1(X1) ),
% 11.74/1.99      inference(renaming,[status(thm)],[c_116]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_650,plain,
% 11.74/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.74/1.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 11.74/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_117]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_7,plain,
% 11.74/1.99      ( ~ r1_tarski(X0,X1)
% 11.74/1.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 11.74/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_659,plain,
% 11.74/1.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 11.74/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_1318,plain,
% 11.74/1.99      ( k1_setfam_1(k6_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(X0)
% 11.74/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.74/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_650,c_659]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_7144,plain,
% 11.74/1.99      ( k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) = k2_relat_1(sK0)
% 11.74/1.99      | v1_relat_1(sK1) != iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_654,c_1318]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_7645,plain,
% 11.74/1.99      ( k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))) = k2_relat_1(sK0) ),
% 11.74/1.99      inference(global_propositional_subsumption,
% 11.74/1.99                [status(thm)],
% 11.74/1.99                [c_7144,c_21]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_8,plain,
% 11.74/1.99      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 11.74/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_658,plain,
% 11.74/1.99      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_2349,plain,
% 11.74/1.99      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_relat_1(sK1))))),k3_relat_1(sK1)) = iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_1985,c_658]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_7660,plain,
% 11.74/1.99      ( r1_tarski(k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k1_setfam_1(k6_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK1))),k2_relat_1(sK0))),k3_relat_1(sK1)) = iProver_top ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_7645,c_2349]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_5,plain,
% 11.74/1.99      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 11.74/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_661,plain,
% 11.74/1.99      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_4,plain,
% 11.74/1.99      ( ~ r1_tarski(X0,X1)
% 11.74/1.99      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 11.74/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_662,plain,
% 11.74/1.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 11.74/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_1410,plain,
% 11.74/1.99      ( k3_tarski(k6_enumset1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) = X0 ),
% 11.74/1.99      inference(superposition,[status(thm)],[c_661,c_662]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_7661,plain,
% 11.74/1.99      ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) = iProver_top ),
% 11.74/1.99      inference(demodulation,[status(thm)],[c_7660,c_1410]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_16,negated_conjecture,
% 11.74/1.99      ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
% 11.74/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_23,plain,
% 11.74/1.99      ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) != iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(c_22,plain,
% 11.74/1.99      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.74/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.74/1.99  
% 11.74/1.99  cnf(contradiction,plain,
% 11.74/1.99      ( $false ),
% 11.74/1.99      inference(minisat,[status(thm)],[c_17337,c_7661,c_23,c_22]) ).
% 11.74/1.99  
% 11.74/1.99  
% 11.74/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.74/1.99  
% 11.74/1.99  ------                               Statistics
% 11.74/1.99  
% 11.74/1.99  ------ General
% 11.74/1.99  
% 11.74/1.99  abstr_ref_over_cycles:                  0
% 11.74/1.99  abstr_ref_under_cycles:                 0
% 11.74/1.99  gc_basic_clause_elim:                   0
% 11.74/1.99  forced_gc_time:                         0
% 11.74/1.99  parsing_time:                           0.005
% 11.74/1.99  unif_index_cands_time:                  0.
% 11.74/1.99  unif_index_add_time:                    0.
% 11.74/1.99  orderings_time:                         0.
% 11.74/1.99  out_proof_time:                         0.011
% 11.74/1.99  total_time:                             1.354
% 11.74/1.99  num_of_symbols:                         40
% 11.74/1.99  num_of_terms:                           19045
% 11.74/1.99  
% 11.74/1.99  ------ Preprocessing
% 11.74/1.99  
% 11.74/1.99  num_of_splits:                          0
% 11.74/1.99  num_of_split_atoms:                     0
% 11.74/1.99  num_of_reused_defs:                     0
% 11.74/1.99  num_eq_ax_congr_red:                    8
% 11.74/1.99  num_of_sem_filtered_clauses:            1
% 11.74/1.99  num_of_subtypes:                        0
% 11.74/1.99  monotx_restored_types:                  0
% 11.74/1.99  sat_num_of_epr_types:                   0
% 11.74/1.99  sat_num_of_non_cyclic_types:            0
% 11.74/1.99  sat_guarded_non_collapsed_types:        0
% 11.74/1.99  num_pure_diseq_elim:                    0
% 11.74/1.99  simp_replaced_by:                       0
% 11.74/1.99  res_preprocessed:                       87
% 11.74/1.99  prep_upred:                             0
% 11.74/1.99  prep_unflattend:                        0
% 11.74/1.99  smt_new_axioms:                         0
% 11.74/1.99  pred_elim_cands:                        2
% 11.74/1.99  pred_elim:                              1
% 11.74/1.99  pred_elim_cl:                           2
% 11.74/1.99  pred_elim_cycles:                       3
% 11.74/1.99  merged_defs:                            2
% 11.74/1.99  merged_defs_ncl:                        0
% 11.74/1.99  bin_hyper_res:                          3
% 11.74/1.99  prep_cycles:                            4
% 11.74/1.99  pred_elim_time:                         0.001
% 11.74/1.99  splitting_time:                         0.
% 11.74/1.99  sem_filter_time:                        0.
% 11.74/1.99  monotx_time:                            0.
% 11.74/1.99  subtype_inf_time:                       0.
% 11.74/1.99  
% 11.74/1.99  ------ Problem properties
% 11.74/1.99  
% 11.74/1.99  clauses:                                17
% 11.74/1.99  conjectures:                            4
% 11.74/1.99  epr:                                    7
% 11.74/1.99  horn:                                   17
% 11.74/1.99  ground:                                 4
% 11.74/1.99  unary:                                  7
% 11.74/1.99  binary:                                 4
% 11.74/1.99  lits:                                   33
% 11.74/1.99  lits_eq:                                4
% 11.74/1.99  fd_pure:                                0
% 11.74/1.99  fd_pseudo:                              0
% 11.74/1.99  fd_cond:                                0
% 11.74/1.99  fd_pseudo_cond:                         1
% 11.74/1.99  ac_symbols:                             0
% 11.74/1.99  
% 11.74/1.99  ------ Propositional Solver
% 11.74/1.99  
% 11.74/1.99  prop_solver_calls:                      33
% 11.74/1.99  prop_fast_solver_calls:                 690
% 11.74/1.99  smt_solver_calls:                       0
% 11.74/1.99  smt_fast_solver_calls:                  0
% 11.74/1.99  prop_num_of_clauses:                    8046
% 11.74/1.99  prop_preprocess_simplified:             16081
% 11.74/1.99  prop_fo_subsumed:                       13
% 11.74/1.99  prop_solver_time:                       0.
% 11.74/1.99  smt_solver_time:                        0.
% 11.74/1.99  smt_fast_solver_time:                   0.
% 11.74/1.99  prop_fast_solver_time:                  0.
% 11.74/1.99  prop_unsat_core_time:                   0.001
% 11.74/1.99  
% 11.74/1.99  ------ QBF
% 11.74/1.99  
% 11.74/1.99  qbf_q_res:                              0
% 11.74/1.99  qbf_num_tautologies:                    0
% 11.74/1.99  qbf_prep_cycles:                        0
% 11.74/1.99  
% 11.74/1.99  ------ BMC1
% 11.74/1.99  
% 11.74/1.99  bmc1_current_bound:                     -1
% 11.74/1.99  bmc1_last_solved_bound:                 -1
% 11.74/1.99  bmc1_unsat_core_size:                   -1
% 11.74/1.99  bmc1_unsat_core_parents_size:           -1
% 11.74/1.99  bmc1_merge_next_fun:                    0
% 11.74/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.74/1.99  
% 11.74/1.99  ------ Instantiation
% 11.74/1.99  
% 11.74/1.99  inst_num_of_clauses:                    1955
% 11.74/1.99  inst_num_in_passive:                    989
% 11.74/1.99  inst_num_in_active:                     726
% 11.74/1.99  inst_num_in_unprocessed:                240
% 11.74/1.99  inst_num_of_loops:                      740
% 11.74/1.99  inst_num_of_learning_restarts:          0
% 11.74/1.99  inst_num_moves_active_passive:          11
% 11.74/1.99  inst_lit_activity:                      0
% 11.74/1.99  inst_lit_activity_moves:                0
% 11.74/1.99  inst_num_tautologies:                   0
% 11.74/1.99  inst_num_prop_implied:                  0
% 11.74/1.99  inst_num_existing_simplified:           0
% 11.74/1.99  inst_num_eq_res_simplified:             0
% 11.74/1.99  inst_num_child_elim:                    0
% 11.74/1.99  inst_num_of_dismatching_blockings:      1555
% 11.74/1.99  inst_num_of_non_proper_insts:           3111
% 11.74/1.99  inst_num_of_duplicates:                 0
% 11.74/1.99  inst_inst_num_from_inst_to_res:         0
% 11.74/1.99  inst_dismatching_checking_time:         0.
% 11.74/1.99  
% 11.74/1.99  ------ Resolution
% 11.74/1.99  
% 11.74/1.99  res_num_of_clauses:                     0
% 11.74/1.99  res_num_in_passive:                     0
% 11.74/1.99  res_num_in_active:                      0
% 11.74/1.99  res_num_of_loops:                       91
% 11.74/1.99  res_forward_subset_subsumed:            457
% 11.74/1.99  res_backward_subset_subsumed:           0
% 11.74/1.99  res_forward_subsumed:                   0
% 11.74/1.99  res_backward_subsumed:                  0
% 11.74/1.99  res_forward_subsumption_resolution:     0
% 11.74/1.99  res_backward_subsumption_resolution:    0
% 11.74/1.99  res_clause_to_clause_subsumption:       2896
% 11.74/1.99  res_orphan_elimination:                 0
% 11.74/1.99  res_tautology_del:                      220
% 11.74/1.99  res_num_eq_res_simplified:              0
% 11.74/1.99  res_num_sel_changes:                    0
% 11.74/1.99  res_moves_from_active_to_pass:          0
% 11.74/1.99  
% 11.74/1.99  ------ Superposition
% 11.74/1.99  
% 11.74/1.99  sup_time_total:                         0.
% 11.74/1.99  sup_time_generating:                    0.
% 11.74/1.99  sup_time_sim_full:                      0.
% 11.74/1.99  sup_time_sim_immed:                     0.
% 11.74/1.99  
% 11.74/1.99  sup_num_of_clauses:                     608
% 11.74/1.99  sup_num_in_active:                      139
% 11.74/1.99  sup_num_in_passive:                     469
% 11.74/1.99  sup_num_of_loops:                       146
% 11.74/1.99  sup_fw_superposition:                   701
% 11.74/1.99  sup_bw_superposition:                   539
% 11.74/1.99  sup_immediate_simplified:               185
% 11.74/1.99  sup_given_eliminated:                   0
% 11.74/1.99  comparisons_done:                       0
% 11.74/1.99  comparisons_avoided:                    0
% 11.74/1.99  
% 11.74/1.99  ------ Simplifications
% 11.74/1.99  
% 11.74/1.99  
% 11.74/1.99  sim_fw_subset_subsumed:                 48
% 11.74/1.99  sim_bw_subset_subsumed:                 6
% 11.74/1.99  sim_fw_subsumed:                        53
% 11.74/1.99  sim_bw_subsumed:                        1
% 11.74/1.99  sim_fw_subsumption_res:                 0
% 11.74/1.99  sim_bw_subsumption_res:                 0
% 11.74/1.99  sim_tautology_del:                      57
% 11.74/1.99  sim_eq_tautology_del:                   13
% 11.74/1.99  sim_eq_res_simp:                        0
% 11.74/1.99  sim_fw_demodulated:                     84
% 11.74/1.99  sim_bw_demodulated:                     12
% 11.74/1.99  sim_light_normalised:                   14
% 11.74/1.99  sim_joinable_taut:                      0
% 11.74/1.99  sim_joinable_simp:                      0
% 11.74/1.99  sim_ac_normalised:                      0
% 11.74/1.99  sim_smt_subsumption:                    0
% 11.74/1.99  
%------------------------------------------------------------------------------

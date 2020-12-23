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
% DateTime   : Thu Dec  3 11:42:22 EST 2020

% Result     : Theorem 11.85s
% Output     : CNFRefutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 909 expanded)
%              Number of clauses        :  103 ( 149 expanded)
%              Number of leaves         :   34 ( 253 expanded)
%              Depth                    :   19
%              Number of atoms          :  601 (1809 expanded)
%              Number of equality atoms :  365 (1306 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f115])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f116])).

fof(f118,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f117])).

fof(f119,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f118])).

fof(f122,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f119])).

fof(f126,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f73,f122])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f103,f122])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f20,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f123,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f102,f83])).

fof(f132,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f84,f123])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f133,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f100,f83])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f29,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f41,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f42,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f41])).

fof(f60,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1)
        & k1_tarski(X0) = X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4)
      & k1_tarski(sK3) = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4)
    & k1_tarski(sK3) = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f60])).

fof(f113,plain,(
    k1_tarski(sK3) = sK4 ),
    inference(cnf_transformation,[],[f61])).

fof(f137,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(definition_unfolding,[],[f113,f122])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f122])).

fof(f112,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f61])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f39])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f48])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f76,f122,f122])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f43,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f32,f44,f43])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f149,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f98])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X10,X8)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f55,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f55])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f56])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f78,f122,f122])).

fof(f139,plain,(
    ! [X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f129])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f71,f122])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f142,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X2,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f96])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f120,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f107,f119])).

fof(f121,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f120])).

fof(f128,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f74,f121,f122,f122,f122])).

fof(f138,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f128])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f24,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f135,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f106,f122])).

fof(f114,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f136,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(definition_unfolding,[],[f114,f122])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f148,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f90])).

cnf(c_3,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_31,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1772,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6155,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1772])).

cnf(c_13,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1768,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
    | r2_hidden(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1768])).

cnf(c_9623,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))) = iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6155,c_4684])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_65,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_67,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_29,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_68,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1774,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1790,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4694,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1774,c_1790])).

cnf(c_4697,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4694])).

cnf(c_33361,plain,
    ( r2_hidden(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9623,c_65,c_67,c_68,c_4694,c_4697])).

cnf(c_40,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1798,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7834,plain,
    ( r2_hidden(sK3,X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_40,c_1798])).

cnf(c_33369,plain,
    ( r1_tarski(sK4,k7_setfam_1(sK3,k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_33361,c_7834])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1765,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1770,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4537,plain,
    ( k7_setfam_1(sK3,k7_setfam_1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_1765,c_1770])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1766,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4539,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4537,c_1766])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2544,plain,
    ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2545,plain,
    ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2544])).

cnf(c_5159,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
    | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4539,c_42,c_2545])).

cnf(c_33375,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_33369,c_5159])).

cnf(c_34010,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6155,c_33375])).

cnf(c_7785,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_7786,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7785])).

cnf(c_17978,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r2_hidden(X0,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17982,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17978])).

cnf(c_17984,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_17982])).

cnf(c_24918,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_24919,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24918])).

cnf(c_34013,plain,
    ( r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34010,c_7786,c_17984,c_24919])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_1794,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8975,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1794])).

cnf(c_8978,plain,
    ( k1_zfmisc_1(k1_xboole_0) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8975,c_3])).

cnf(c_34017,plain,
    ( k7_setfam_1(sK3,sK4) = k1_zfmisc_1(k1_xboole_0)
    | k7_setfam_1(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34013,c_8978])).

cnf(c_6158,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_1790])).

cnf(c_28,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_1775,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5728,plain,
    ( sP1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1775])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | ~ r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1786,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) = iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9752,plain,
    ( sP0(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5728,c_1786])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X1 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1777,plain,
    ( X0 = X1
    | X2 = X1
    | X3 = X1
    | X4 = X1
    | X5 = X1
    | X6 = X1
    | X7 = X1
    | X8 = X1
    | sP0(X1,X0,X8,X7,X6,X5,X4,X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23553,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9752,c_1777])).

cnf(c_23562,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6158,c_23553])).

cnf(c_23571,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_23562])).

cnf(c_1010,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_21773,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k7_setfam_1(sK3,sK4))
    | X0 != X2
    | X1 != k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_21779,plain,
    ( X0 != X1
    | X2 != k7_setfam_1(sK3,sK4)
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,k7_setfam_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21773])).

cnf(c_21781,plain,
    ( k1_xboole_0 != k7_setfam_1(sK3,sK4)
    | k1_xboole_0 != k1_xboole_0
    | r2_hidden(k1_xboole_0,k7_setfam_1(sK3,sK4)) != iProver_top
    | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_21779])).

cnf(c_6,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_1796,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9018,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_40,c_1796])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1797,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6290,plain,
    ( r2_hidden(sK3,X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_40,c_1797])).

cnf(c_9027,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_9018,c_6290])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1767,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4540,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK3,sK4)) = iProver_top
    | r2_hidden(k3_subset_1(sK3,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4537,c_1767])).

cnf(c_5035,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK3,sK4)) = iProver_top
    | r2_hidden(k3_subset_1(sK3,X0),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4540,c_42,c_2545])).

cnf(c_5041,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | r2_hidden(k1_xboole_0,k7_setfam_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_5035])).

cnf(c_19,plain,
    ( sP0(X0,X1,X0,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_2133,plain,
    ( sP0(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0,X1,X2,X3,X4,X5,X6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2134,plain,
    ( sP0(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0,X1,X2,X3,X4,X5,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2133])).

cnf(c_2136,plain,
    ( sP0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_1017,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8)
    | X9 != X0 ),
    theory(equality)).

cnf(c_1906,plain,
    ( ~ sP0(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1,X2,X3,X4,X5,X6,X7)
    | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1,X2,X3,X4,X5,X6,X7)
    | k7_setfam_1(sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_1907,plain,
    ( k7_setfam_1(sK3,sK4) != X0
    | sP0(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1,X2,X3,X4,X5,X6,X7) != iProver_top
    | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1906])).

cnf(c_1909,plain,
    ( k7_setfam_1(sK3,sK4) != k1_xboole_0
    | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | sP0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1907])).

cnf(c_1838,plain,
    ( ~ sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0,X1,X2,X3,X4,X5,X6)
    | X6 = k7_setfam_1(sK3,sK4)
    | X5 = k7_setfam_1(sK3,sK4)
    | X4 = k7_setfam_1(sK3,sK4)
    | X3 = k7_setfam_1(sK3,sK4)
    | X2 = k7_setfam_1(sK3,sK4)
    | X1 = k7_setfam_1(sK3,sK4)
    | X0 = k7_setfam_1(sK3,sK4)
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k7_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1839,plain,
    ( X0 = k7_setfam_1(sK3,sK4)
    | X1 = k7_setfam_1(sK3,sK4)
    | X2 = k7_setfam_1(sK3,sK4)
    | X3 = k7_setfam_1(sK3,sK4)
    | X4 = k7_setfam_1(sK3,sK4)
    | X5 = k7_setfam_1(sK3,sK4)
    | X6 = k7_setfam_1(sK3,sK4)
    | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k7_setfam_1(sK3,sK4)
    | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X6,X5,X4,X3,X2,X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1838])).

cnf(c_1841,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k7_setfam_1(sK3,sK4)
    | k1_xboole_0 = k7_setfam_1(sK3,sK4)
    | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_5,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1800,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5,c_0,c_34])).

cnf(c_1820,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1800])).

cnf(c_39,negated_conjecture,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1799,plain,
    ( k7_setfam_1(sK3,sK4) != k1_zfmisc_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_39,c_3])).

cnf(c_25,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_81,plain,
    ( sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_78,plain,
    ( ~ sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34017,c_23571,c_21781,c_9027,c_7786,c_5041,c_2136,c_1909,c_1841,c_1820,c_1799,c_81,c_78,c_67,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:42:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.85/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.85/1.99  
% 11.85/1.99  ------  iProver source info
% 11.85/1.99  
% 11.85/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.85/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.85/1.99  git: non_committed_changes: false
% 11.85/1.99  git: last_make_outside_of_git: false
% 11.85/1.99  
% 11.85/1.99  ------ 
% 11.85/1.99  
% 11.85/1.99  ------ Input Options
% 11.85/1.99  
% 11.85/1.99  --out_options                           all
% 11.85/1.99  --tptp_safe_out                         true
% 11.85/1.99  --problem_path                          ""
% 11.85/1.99  --include_path                          ""
% 11.85/1.99  --clausifier                            res/vclausify_rel
% 11.85/1.99  --clausifier_options                    ""
% 11.85/1.99  --stdin                                 false
% 11.85/1.99  --stats_out                             all
% 11.85/1.99  
% 11.85/1.99  ------ General Options
% 11.85/1.99  
% 11.85/1.99  --fof                                   false
% 11.85/1.99  --time_out_real                         305.
% 11.85/1.99  --time_out_virtual                      -1.
% 11.85/1.99  --symbol_type_check                     false
% 11.85/1.99  --clausify_out                          false
% 11.85/1.99  --sig_cnt_out                           false
% 11.85/1.99  --trig_cnt_out                          false
% 11.85/1.99  --trig_cnt_out_tolerance                1.
% 11.85/1.99  --trig_cnt_out_sk_spl                   false
% 11.85/1.99  --abstr_cl_out                          false
% 11.85/1.99  
% 11.85/1.99  ------ Global Options
% 11.85/1.99  
% 11.85/1.99  --schedule                              default
% 11.85/1.99  --add_important_lit                     false
% 11.85/1.99  --prop_solver_per_cl                    1000
% 11.85/1.99  --min_unsat_core                        false
% 11.85/1.99  --soft_assumptions                      false
% 11.85/1.99  --soft_lemma_size                       3
% 11.85/1.99  --prop_impl_unit_size                   0
% 11.85/1.99  --prop_impl_unit                        []
% 11.85/1.99  --share_sel_clauses                     true
% 11.85/1.99  --reset_solvers                         false
% 11.85/1.99  --bc_imp_inh                            [conj_cone]
% 11.85/1.99  --conj_cone_tolerance                   3.
% 11.85/1.99  --extra_neg_conj                        none
% 11.85/1.99  --large_theory_mode                     true
% 11.85/1.99  --prolific_symb_bound                   200
% 11.85/1.99  --lt_threshold                          2000
% 11.85/1.99  --clause_weak_htbl                      true
% 11.85/1.99  --gc_record_bc_elim                     false
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing Options
% 11.85/1.99  
% 11.85/1.99  --preprocessing_flag                    true
% 11.85/1.99  --time_out_prep_mult                    0.1
% 11.85/1.99  --splitting_mode                        input
% 11.85/1.99  --splitting_grd                         true
% 11.85/1.99  --splitting_cvd                         false
% 11.85/1.99  --splitting_cvd_svl                     false
% 11.85/1.99  --splitting_nvd                         32
% 11.85/1.99  --sub_typing                            true
% 11.85/1.99  --prep_gs_sim                           true
% 11.85/1.99  --prep_unflatten                        true
% 11.85/1.99  --prep_res_sim                          true
% 11.85/1.99  --prep_upred                            true
% 11.85/1.99  --prep_sem_filter                       exhaustive
% 11.85/1.99  --prep_sem_filter_out                   false
% 11.85/1.99  --pred_elim                             true
% 11.85/1.99  --res_sim_input                         true
% 11.85/1.99  --eq_ax_congr_red                       true
% 11.85/1.99  --pure_diseq_elim                       true
% 11.85/1.99  --brand_transform                       false
% 11.85/1.99  --non_eq_to_eq                          false
% 11.85/1.99  --prep_def_merge                        true
% 11.85/1.99  --prep_def_merge_prop_impl              false
% 11.85/1.99  --prep_def_merge_mbd                    true
% 11.85/1.99  --prep_def_merge_tr_red                 false
% 11.85/1.99  --prep_def_merge_tr_cl                  false
% 11.85/1.99  --smt_preprocessing                     true
% 11.85/1.99  --smt_ac_axioms                         fast
% 11.85/1.99  --preprocessed_out                      false
% 11.85/1.99  --preprocessed_stats                    false
% 11.85/1.99  
% 11.85/1.99  ------ Abstraction refinement Options
% 11.85/1.99  
% 11.85/1.99  --abstr_ref                             []
% 11.85/1.99  --abstr_ref_prep                        false
% 11.85/1.99  --abstr_ref_until_sat                   false
% 11.85/1.99  --abstr_ref_sig_restrict                funpre
% 11.85/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/1.99  --abstr_ref_under                       []
% 11.85/1.99  
% 11.85/1.99  ------ SAT Options
% 11.85/1.99  
% 11.85/1.99  --sat_mode                              false
% 11.85/1.99  --sat_fm_restart_options                ""
% 11.85/1.99  --sat_gr_def                            false
% 11.85/1.99  --sat_epr_types                         true
% 11.85/1.99  --sat_non_cyclic_types                  false
% 11.85/1.99  --sat_finite_models                     false
% 11.85/1.99  --sat_fm_lemmas                         false
% 11.85/1.99  --sat_fm_prep                           false
% 11.85/1.99  --sat_fm_uc_incr                        true
% 11.85/1.99  --sat_out_model                         small
% 11.85/1.99  --sat_out_clauses                       false
% 11.85/1.99  
% 11.85/1.99  ------ QBF Options
% 11.85/1.99  
% 11.85/1.99  --qbf_mode                              false
% 11.85/1.99  --qbf_elim_univ                         false
% 11.85/1.99  --qbf_dom_inst                          none
% 11.85/1.99  --qbf_dom_pre_inst                      false
% 11.85/1.99  --qbf_sk_in                             false
% 11.85/1.99  --qbf_pred_elim                         true
% 11.85/1.99  --qbf_split                             512
% 11.85/1.99  
% 11.85/1.99  ------ BMC1 Options
% 11.85/1.99  
% 11.85/1.99  --bmc1_incremental                      false
% 11.85/1.99  --bmc1_axioms                           reachable_all
% 11.85/1.99  --bmc1_min_bound                        0
% 11.85/1.99  --bmc1_max_bound                        -1
% 11.85/1.99  --bmc1_max_bound_default                -1
% 11.85/1.99  --bmc1_symbol_reachability              true
% 11.85/1.99  --bmc1_property_lemmas                  false
% 11.85/1.99  --bmc1_k_induction                      false
% 11.85/1.99  --bmc1_non_equiv_states                 false
% 11.85/1.99  --bmc1_deadlock                         false
% 11.85/1.99  --bmc1_ucm                              false
% 11.85/1.99  --bmc1_add_unsat_core                   none
% 11.85/1.99  --bmc1_unsat_core_children              false
% 11.85/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/1.99  --bmc1_out_stat                         full
% 11.85/1.99  --bmc1_ground_init                      false
% 11.85/1.99  --bmc1_pre_inst_next_state              false
% 11.85/1.99  --bmc1_pre_inst_state                   false
% 11.85/1.99  --bmc1_pre_inst_reach_state             false
% 11.85/1.99  --bmc1_out_unsat_core                   false
% 11.85/1.99  --bmc1_aig_witness_out                  false
% 11.85/1.99  --bmc1_verbose                          false
% 11.85/1.99  --bmc1_dump_clauses_tptp                false
% 11.85/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.85/1.99  --bmc1_dump_file                        -
% 11.85/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.85/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.85/1.99  --bmc1_ucm_extend_mode                  1
% 11.85/1.99  --bmc1_ucm_init_mode                    2
% 11.85/1.99  --bmc1_ucm_cone_mode                    none
% 11.85/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.85/1.99  --bmc1_ucm_relax_model                  4
% 11.85/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.85/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/1.99  --bmc1_ucm_layered_model                none
% 11.85/1.99  --bmc1_ucm_max_lemma_size               10
% 11.85/1.99  
% 11.85/1.99  ------ AIG Options
% 11.85/1.99  
% 11.85/1.99  --aig_mode                              false
% 11.85/1.99  
% 11.85/1.99  ------ Instantiation Options
% 11.85/1.99  
% 11.85/1.99  --instantiation_flag                    true
% 11.85/1.99  --inst_sos_flag                         true
% 11.85/1.99  --inst_sos_phase                        true
% 11.85/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/1.99  --inst_lit_sel_side                     num_symb
% 11.85/1.99  --inst_solver_per_active                1400
% 11.85/1.99  --inst_solver_calls_frac                1.
% 11.85/1.99  --inst_passive_queue_type               priority_queues
% 11.85/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/1.99  --inst_passive_queues_freq              [25;2]
% 11.85/1.99  --inst_dismatching                      true
% 11.85/1.99  --inst_eager_unprocessed_to_passive     true
% 11.85/1.99  --inst_prop_sim_given                   true
% 11.85/1.99  --inst_prop_sim_new                     false
% 11.85/1.99  --inst_subs_new                         false
% 11.85/1.99  --inst_eq_res_simp                      false
% 11.85/1.99  --inst_subs_given                       false
% 11.85/1.99  --inst_orphan_elimination               true
% 11.85/1.99  --inst_learning_loop_flag               true
% 11.85/1.99  --inst_learning_start                   3000
% 11.85/1.99  --inst_learning_factor                  2
% 11.85/1.99  --inst_start_prop_sim_after_learn       3
% 11.85/1.99  --inst_sel_renew                        solver
% 11.85/1.99  --inst_lit_activity_flag                true
% 11.85/1.99  --inst_restr_to_given                   false
% 11.85/1.99  --inst_activity_threshold               500
% 11.85/1.99  --inst_out_proof                        true
% 11.85/1.99  
% 11.85/1.99  ------ Resolution Options
% 11.85/1.99  
% 11.85/1.99  --resolution_flag                       true
% 11.85/1.99  --res_lit_sel                           adaptive
% 11.85/1.99  --res_lit_sel_side                      none
% 11.85/1.99  --res_ordering                          kbo
% 11.85/1.99  --res_to_prop_solver                    active
% 11.85/1.99  --res_prop_simpl_new                    false
% 11.85/1.99  --res_prop_simpl_given                  true
% 11.85/1.99  --res_passive_queue_type                priority_queues
% 11.85/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/1.99  --res_passive_queues_freq               [15;5]
% 11.85/1.99  --res_forward_subs                      full
% 11.85/1.99  --res_backward_subs                     full
% 11.85/1.99  --res_forward_subs_resolution           true
% 11.85/1.99  --res_backward_subs_resolution          true
% 11.85/1.99  --res_orphan_elimination                true
% 11.85/1.99  --res_time_limit                        2.
% 11.85/1.99  --res_out_proof                         true
% 11.85/1.99  
% 11.85/1.99  ------ Superposition Options
% 11.85/1.99  
% 11.85/1.99  --superposition_flag                    true
% 11.85/1.99  --sup_passive_queue_type                priority_queues
% 11.85/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.85/1.99  --demod_completeness_check              fast
% 11.85/1.99  --demod_use_ground                      true
% 11.85/1.99  --sup_to_prop_solver                    passive
% 11.85/1.99  --sup_prop_simpl_new                    true
% 11.85/1.99  --sup_prop_simpl_given                  true
% 11.85/1.99  --sup_fun_splitting                     true
% 11.85/1.99  --sup_smt_interval                      50000
% 11.85/1.99  
% 11.85/1.99  ------ Superposition Simplification Setup
% 11.85/1.99  
% 11.85/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/1.99  --sup_immed_triv                        [TrivRules]
% 11.85/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_immed_bw_main                     []
% 11.85/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_input_bw                          []
% 11.85/1.99  
% 11.85/1.99  ------ Combination Options
% 11.85/1.99  
% 11.85/1.99  --comb_res_mult                         3
% 11.85/1.99  --comb_sup_mult                         2
% 11.85/1.99  --comb_inst_mult                        10
% 11.85/1.99  
% 11.85/1.99  ------ Debug Options
% 11.85/1.99  
% 11.85/1.99  --dbg_backtrace                         false
% 11.85/1.99  --dbg_dump_prop_clauses                 false
% 11.85/1.99  --dbg_dump_prop_clauses_file            -
% 11.85/1.99  --dbg_out_stat                          false
% 11.85/1.99  ------ Parsing...
% 11.85/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.85/1.99  ------ Proving...
% 11.85/1.99  ------ Problem Properties 
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  clauses                                 42
% 11.85/1.99  conjectures                             3
% 11.85/1.99  EPR                                     15
% 11.85/1.99  Horn                                    36
% 11.85/1.99  unary                                   21
% 11.85/1.99  binary                                  7
% 11.85/1.99  lits                                    86
% 11.85/1.99  lits eq                                 23
% 11.85/1.99  fd_pure                                 0
% 11.85/1.99  fd_pseudo                               0
% 11.85/1.99  fd_cond                                 1
% 11.85/1.99  fd_pseudo_cond                          4
% 11.85/1.99  AC symbols                              0
% 11.85/1.99  
% 11.85/1.99  ------ Schedule dynamic 5 is on 
% 11.85/1.99  
% 11.85/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  ------ 
% 11.85/1.99  Current options:
% 11.85/1.99  ------ 
% 11.85/1.99  
% 11.85/1.99  ------ Input Options
% 11.85/1.99  
% 11.85/1.99  --out_options                           all
% 11.85/1.99  --tptp_safe_out                         true
% 11.85/1.99  --problem_path                          ""
% 11.85/1.99  --include_path                          ""
% 11.85/1.99  --clausifier                            res/vclausify_rel
% 11.85/1.99  --clausifier_options                    ""
% 11.85/1.99  --stdin                                 false
% 11.85/1.99  --stats_out                             all
% 11.85/1.99  
% 11.85/1.99  ------ General Options
% 11.85/1.99  
% 11.85/1.99  --fof                                   false
% 11.85/1.99  --time_out_real                         305.
% 11.85/1.99  --time_out_virtual                      -1.
% 11.85/1.99  --symbol_type_check                     false
% 11.85/1.99  --clausify_out                          false
% 11.85/1.99  --sig_cnt_out                           false
% 11.85/1.99  --trig_cnt_out                          false
% 11.85/1.99  --trig_cnt_out_tolerance                1.
% 11.85/1.99  --trig_cnt_out_sk_spl                   false
% 11.85/1.99  --abstr_cl_out                          false
% 11.85/1.99  
% 11.85/1.99  ------ Global Options
% 11.85/1.99  
% 11.85/1.99  --schedule                              default
% 11.85/1.99  --add_important_lit                     false
% 11.85/1.99  --prop_solver_per_cl                    1000
% 11.85/1.99  --min_unsat_core                        false
% 11.85/1.99  --soft_assumptions                      false
% 11.85/1.99  --soft_lemma_size                       3
% 11.85/1.99  --prop_impl_unit_size                   0
% 11.85/1.99  --prop_impl_unit                        []
% 11.85/1.99  --share_sel_clauses                     true
% 11.85/1.99  --reset_solvers                         false
% 11.85/1.99  --bc_imp_inh                            [conj_cone]
% 11.85/1.99  --conj_cone_tolerance                   3.
% 11.85/1.99  --extra_neg_conj                        none
% 11.85/1.99  --large_theory_mode                     true
% 11.85/1.99  --prolific_symb_bound                   200
% 11.85/1.99  --lt_threshold                          2000
% 11.85/1.99  --clause_weak_htbl                      true
% 11.85/1.99  --gc_record_bc_elim                     false
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing Options
% 11.85/1.99  
% 11.85/1.99  --preprocessing_flag                    true
% 11.85/1.99  --time_out_prep_mult                    0.1
% 11.85/1.99  --splitting_mode                        input
% 11.85/1.99  --splitting_grd                         true
% 11.85/1.99  --splitting_cvd                         false
% 11.85/1.99  --splitting_cvd_svl                     false
% 11.85/1.99  --splitting_nvd                         32
% 11.85/1.99  --sub_typing                            true
% 11.85/1.99  --prep_gs_sim                           true
% 11.85/1.99  --prep_unflatten                        true
% 11.85/1.99  --prep_res_sim                          true
% 11.85/1.99  --prep_upred                            true
% 11.85/1.99  --prep_sem_filter                       exhaustive
% 11.85/1.99  --prep_sem_filter_out                   false
% 11.85/1.99  --pred_elim                             true
% 11.85/1.99  --res_sim_input                         true
% 11.85/1.99  --eq_ax_congr_red                       true
% 11.85/1.99  --pure_diseq_elim                       true
% 11.85/1.99  --brand_transform                       false
% 11.85/1.99  --non_eq_to_eq                          false
% 11.85/1.99  --prep_def_merge                        true
% 11.85/1.99  --prep_def_merge_prop_impl              false
% 11.85/1.99  --prep_def_merge_mbd                    true
% 11.85/1.99  --prep_def_merge_tr_red                 false
% 11.85/1.99  --prep_def_merge_tr_cl                  false
% 11.85/1.99  --smt_preprocessing                     true
% 11.85/1.99  --smt_ac_axioms                         fast
% 11.85/1.99  --preprocessed_out                      false
% 11.85/1.99  --preprocessed_stats                    false
% 11.85/1.99  
% 11.85/1.99  ------ Abstraction refinement Options
% 11.85/1.99  
% 11.85/1.99  --abstr_ref                             []
% 11.85/1.99  --abstr_ref_prep                        false
% 11.85/1.99  --abstr_ref_until_sat                   false
% 11.85/1.99  --abstr_ref_sig_restrict                funpre
% 11.85/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/1.99  --abstr_ref_under                       []
% 11.85/1.99  
% 11.85/1.99  ------ SAT Options
% 11.85/1.99  
% 11.85/1.99  --sat_mode                              false
% 11.85/1.99  --sat_fm_restart_options                ""
% 11.85/1.99  --sat_gr_def                            false
% 11.85/1.99  --sat_epr_types                         true
% 11.85/1.99  --sat_non_cyclic_types                  false
% 11.85/1.99  --sat_finite_models                     false
% 11.85/1.99  --sat_fm_lemmas                         false
% 11.85/1.99  --sat_fm_prep                           false
% 11.85/1.99  --sat_fm_uc_incr                        true
% 11.85/1.99  --sat_out_model                         small
% 11.85/1.99  --sat_out_clauses                       false
% 11.85/1.99  
% 11.85/1.99  ------ QBF Options
% 11.85/1.99  
% 11.85/1.99  --qbf_mode                              false
% 11.85/1.99  --qbf_elim_univ                         false
% 11.85/1.99  --qbf_dom_inst                          none
% 11.85/1.99  --qbf_dom_pre_inst                      false
% 11.85/1.99  --qbf_sk_in                             false
% 11.85/1.99  --qbf_pred_elim                         true
% 11.85/1.99  --qbf_split                             512
% 11.85/1.99  
% 11.85/1.99  ------ BMC1 Options
% 11.85/1.99  
% 11.85/1.99  --bmc1_incremental                      false
% 11.85/1.99  --bmc1_axioms                           reachable_all
% 11.85/1.99  --bmc1_min_bound                        0
% 11.85/1.99  --bmc1_max_bound                        -1
% 11.85/1.99  --bmc1_max_bound_default                -1
% 11.85/1.99  --bmc1_symbol_reachability              true
% 11.85/1.99  --bmc1_property_lemmas                  false
% 11.85/1.99  --bmc1_k_induction                      false
% 11.85/1.99  --bmc1_non_equiv_states                 false
% 11.85/1.99  --bmc1_deadlock                         false
% 11.85/1.99  --bmc1_ucm                              false
% 11.85/1.99  --bmc1_add_unsat_core                   none
% 11.85/1.99  --bmc1_unsat_core_children              false
% 11.85/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/1.99  --bmc1_out_stat                         full
% 11.85/1.99  --bmc1_ground_init                      false
% 11.85/1.99  --bmc1_pre_inst_next_state              false
% 11.85/1.99  --bmc1_pre_inst_state                   false
% 11.85/1.99  --bmc1_pre_inst_reach_state             false
% 11.85/1.99  --bmc1_out_unsat_core                   false
% 11.85/1.99  --bmc1_aig_witness_out                  false
% 11.85/1.99  --bmc1_verbose                          false
% 11.85/1.99  --bmc1_dump_clauses_tptp                false
% 11.85/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.85/1.99  --bmc1_dump_file                        -
% 11.85/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.85/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.85/1.99  --bmc1_ucm_extend_mode                  1
% 11.85/1.99  --bmc1_ucm_init_mode                    2
% 11.85/1.99  --bmc1_ucm_cone_mode                    none
% 11.85/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.85/1.99  --bmc1_ucm_relax_model                  4
% 11.85/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.85/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/1.99  --bmc1_ucm_layered_model                none
% 11.85/1.99  --bmc1_ucm_max_lemma_size               10
% 11.85/1.99  
% 11.85/1.99  ------ AIG Options
% 11.85/1.99  
% 11.85/1.99  --aig_mode                              false
% 11.85/1.99  
% 11.85/1.99  ------ Instantiation Options
% 11.85/1.99  
% 11.85/1.99  --instantiation_flag                    true
% 11.85/1.99  --inst_sos_flag                         true
% 11.85/1.99  --inst_sos_phase                        true
% 11.85/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/1.99  --inst_lit_sel_side                     none
% 11.85/1.99  --inst_solver_per_active                1400
% 11.85/1.99  --inst_solver_calls_frac                1.
% 11.85/1.99  --inst_passive_queue_type               priority_queues
% 11.85/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/1.99  --inst_passive_queues_freq              [25;2]
% 11.85/1.99  --inst_dismatching                      true
% 11.85/1.99  --inst_eager_unprocessed_to_passive     true
% 11.85/1.99  --inst_prop_sim_given                   true
% 11.85/1.99  --inst_prop_sim_new                     false
% 11.85/1.99  --inst_subs_new                         false
% 11.85/1.99  --inst_eq_res_simp                      false
% 11.85/1.99  --inst_subs_given                       false
% 11.85/1.99  --inst_orphan_elimination               true
% 11.85/1.99  --inst_learning_loop_flag               true
% 11.85/1.99  --inst_learning_start                   3000
% 11.85/1.99  --inst_learning_factor                  2
% 11.85/1.99  --inst_start_prop_sim_after_learn       3
% 11.85/1.99  --inst_sel_renew                        solver
% 11.85/1.99  --inst_lit_activity_flag                true
% 11.85/1.99  --inst_restr_to_given                   false
% 11.85/1.99  --inst_activity_threshold               500
% 11.85/1.99  --inst_out_proof                        true
% 11.85/1.99  
% 11.85/1.99  ------ Resolution Options
% 11.85/1.99  
% 11.85/1.99  --resolution_flag                       false
% 11.85/1.99  --res_lit_sel                           adaptive
% 11.85/1.99  --res_lit_sel_side                      none
% 11.85/1.99  --res_ordering                          kbo
% 11.85/1.99  --res_to_prop_solver                    active
% 11.85/1.99  --res_prop_simpl_new                    false
% 11.85/1.99  --res_prop_simpl_given                  true
% 11.85/1.99  --res_passive_queue_type                priority_queues
% 11.85/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/1.99  --res_passive_queues_freq               [15;5]
% 11.85/1.99  --res_forward_subs                      full
% 11.85/1.99  --res_backward_subs                     full
% 11.85/1.99  --res_forward_subs_resolution           true
% 11.85/1.99  --res_backward_subs_resolution          true
% 11.85/1.99  --res_orphan_elimination                true
% 11.85/1.99  --res_time_limit                        2.
% 11.85/1.99  --res_out_proof                         true
% 11.85/1.99  
% 11.85/1.99  ------ Superposition Options
% 11.85/1.99  
% 11.85/1.99  --superposition_flag                    true
% 11.85/1.99  --sup_passive_queue_type                priority_queues
% 11.85/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.85/1.99  --demod_completeness_check              fast
% 11.85/1.99  --demod_use_ground                      true
% 11.85/1.99  --sup_to_prop_solver                    passive
% 11.85/1.99  --sup_prop_simpl_new                    true
% 11.85/1.99  --sup_prop_simpl_given                  true
% 11.85/1.99  --sup_fun_splitting                     true
% 11.85/1.99  --sup_smt_interval                      50000
% 11.85/1.99  
% 11.85/1.99  ------ Superposition Simplification Setup
% 11.85/1.99  
% 11.85/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/1.99  --sup_immed_triv                        [TrivRules]
% 11.85/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_immed_bw_main                     []
% 11.85/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/1.99  --sup_input_bw                          []
% 11.85/1.99  
% 11.85/1.99  ------ Combination Options
% 11.85/1.99  
% 11.85/1.99  --comb_res_mult                         3
% 11.85/1.99  --comb_sup_mult                         2
% 11.85/1.99  --comb_inst_mult                        10
% 11.85/1.99  
% 11.85/1.99  ------ Debug Options
% 11.85/1.99  
% 11.85/1.99  --dbg_backtrace                         false
% 11.85/1.99  --dbg_dump_prop_clauses                 false
% 11.85/1.99  --dbg_dump_prop_clauses_file            -
% 11.85/1.99  --dbg_out_stat                          false
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  ------ Proving...
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  % SZS status Theorem for theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  fof(f11,axiom,(
% 11.85/1.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f73,plain,(
% 11.85/1.99    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 11.85/1.99    inference(cnf_transformation,[],[f11])).
% 11.85/1.99  
% 11.85/1.99  fof(f3,axiom,(
% 11.85/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f64,plain,(
% 11.85/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f3])).
% 11.85/1.99  
% 11.85/1.99  fof(f4,axiom,(
% 11.85/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f65,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f4])).
% 11.85/1.99  
% 11.85/1.99  fof(f5,axiom,(
% 11.85/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f66,plain,(
% 11.85/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f5])).
% 11.85/1.99  
% 11.85/1.99  fof(f6,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f67,plain,(
% 11.85/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f6])).
% 11.85/1.99  
% 11.85/1.99  fof(f7,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f68,plain,(
% 11.85/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f7])).
% 11.85/1.99  
% 11.85/1.99  fof(f8,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f69,plain,(
% 11.85/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f8])).
% 11.85/1.99  
% 11.85/1.99  fof(f9,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f70,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f9])).
% 11.85/1.99  
% 11.85/1.99  fof(f115,plain,(
% 11.85/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f69,f70])).
% 11.85/1.99  
% 11.85/1.99  fof(f116,plain,(
% 11.85/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f68,f115])).
% 11.85/1.99  
% 11.85/1.99  fof(f117,plain,(
% 11.85/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f67,f116])).
% 11.85/1.99  
% 11.85/1.99  fof(f118,plain,(
% 11.85/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f66,f117])).
% 11.85/1.99  
% 11.85/1.99  fof(f119,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f65,f118])).
% 11.85/1.99  
% 11.85/1.99  fof(f122,plain,(
% 11.85/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f64,f119])).
% 11.85/1.99  
% 11.85/1.99  fof(f126,plain,(
% 11.85/1.99    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 11.85/1.99    inference(definition_unfolding,[],[f73,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f21,axiom,(
% 11.85/1.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f33,plain,(
% 11.85/1.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 11.85/1.99    inference(ennf_transformation,[],[f21])).
% 11.85/1.99  
% 11.85/1.99  fof(f103,plain,(
% 11.85/1.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f33])).
% 11.85/1.99  
% 11.85/1.99  fof(f134,plain,(
% 11.85/1.99    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f103,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f16,axiom,(
% 11.85/1.99    ! [X0] : k2_subset_1(X0) = X0),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f84,plain,(
% 11.85/1.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.85/1.99    inference(cnf_transformation,[],[f16])).
% 11.85/1.99  
% 11.85/1.99  fof(f20,axiom,(
% 11.85/1.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f102,plain,(
% 11.85/1.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f20])).
% 11.85/1.99  
% 11.85/1.99  fof(f15,axiom,(
% 11.85/1.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f83,plain,(
% 11.85/1.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f15])).
% 11.85/1.99  
% 11.85/1.99  fof(f123,plain,(
% 11.85/1.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f102,f83])).
% 11.85/1.99  
% 11.85/1.99  fof(f132,plain,(
% 11.85/1.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 11.85/1.99    inference(definition_unfolding,[],[f84,f123])).
% 11.85/1.99  
% 11.85/1.99  fof(f27,axiom,(
% 11.85/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f38,plain,(
% 11.85/1.99    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    inference(ennf_transformation,[],[f27])).
% 11.85/1.99  
% 11.85/1.99  fof(f59,plain,(
% 11.85/1.99    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    inference(nnf_transformation,[],[f38])).
% 11.85/1.99  
% 11.85/1.99  fof(f110,plain,(
% 11.85/1.99    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f59])).
% 11.85/1.99  
% 11.85/1.99  fof(f19,axiom,(
% 11.85/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f101,plain,(
% 11.85/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f19])).
% 11.85/1.99  
% 11.85/1.99  fof(f18,axiom,(
% 11.85/1.99    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f100,plain,(
% 11.85/1.99    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f18])).
% 11.85/1.99  
% 11.85/1.99  fof(f133,plain,(
% 11.85/1.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.85/1.99    inference(definition_unfolding,[],[f100,f83])).
% 11.85/1.99  
% 11.85/1.99  fof(f14,axiom,(
% 11.85/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f31,plain,(
% 11.85/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.85/1.99    inference(ennf_transformation,[],[f14])).
% 11.85/1.99  
% 11.85/1.99  fof(f50,plain,(
% 11.85/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.85/1.99    inference(nnf_transformation,[],[f31])).
% 11.85/1.99  
% 11.85/1.99  fof(f79,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f50])).
% 11.85/1.99  
% 11.85/1.99  fof(f29,conjecture,(
% 11.85/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f30,negated_conjecture,(
% 11.85/1.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_tarski(X0) = X1 => k1_tarski(k1_xboole_0) = k7_setfam_1(X0,X1)))),
% 11.85/1.99    inference(negated_conjecture,[],[f29])).
% 11.85/1.99  
% 11.85/1.99  fof(f41,plain,(
% 11.85/1.99    ? [X0,X1] : ((k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    inference(ennf_transformation,[],[f30])).
% 11.85/1.99  
% 11.85/1.99  fof(f42,plain,(
% 11.85/1.99    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    inference(flattening,[],[f41])).
% 11.85/1.99  
% 11.85/1.99  fof(f60,plain,(
% 11.85/1.99    ? [X0,X1] : (k1_tarski(k1_xboole_0) != k7_setfam_1(X0,X1) & k1_tarski(X0) = X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) & k1_tarski(sK3) = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 11.85/1.99    introduced(choice_axiom,[])).
% 11.85/1.99  
% 11.85/1.99  fof(f61,plain,(
% 11.85/1.99    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4) & k1_tarski(sK3) = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 11.85/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f60])).
% 11.85/1.99  
% 11.85/1.99  fof(f113,plain,(
% 11.85/1.99    k1_tarski(sK3) = sK4),
% 11.85/1.99    inference(cnf_transformation,[],[f61])).
% 11.85/1.99  
% 11.85/1.99  fof(f137,plain,(
% 11.85/1.99    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4),
% 11.85/1.99    inference(definition_unfolding,[],[f113,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f10,axiom,(
% 11.85/1.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f46,plain,(
% 11.85/1.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.85/1.99    inference(nnf_transformation,[],[f10])).
% 11.85/1.99  
% 11.85/1.99  fof(f72,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f46])).
% 11.85/1.99  
% 11.85/1.99  fof(f124,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f72,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f112,plain,(
% 11.85/1.99    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 11.85/1.99    inference(cnf_transformation,[],[f61])).
% 11.85/1.99  
% 11.85/1.99  fof(f23,axiom,(
% 11.85/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f35,plain,(
% 11.85/1.99    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    inference(ennf_transformation,[],[f23])).
% 11.85/1.99  
% 11.85/1.99  fof(f105,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f35])).
% 11.85/1.99  
% 11.85/1.99  fof(f28,axiom,(
% 11.85/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f39,plain,(
% 11.85/1.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    inference(ennf_transformation,[],[f28])).
% 11.85/1.99  
% 11.85/1.99  fof(f40,plain,(
% 11.85/1.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    inference(flattening,[],[f39])).
% 11.85/1.99  
% 11.85/1.99  fof(f111,plain,(
% 11.85/1.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f40])).
% 11.85/1.99  
% 11.85/1.99  fof(f22,axiom,(
% 11.85/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f34,plain,(
% 11.85/1.99    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.85/1.99    inference(ennf_transformation,[],[f22])).
% 11.85/1.99  
% 11.85/1.99  fof(f104,plain,(
% 11.85/1.99    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f34])).
% 11.85/1.99  
% 11.85/1.99  fof(f13,axiom,(
% 11.85/1.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f48,plain,(
% 11.85/1.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.85/1.99    inference(nnf_transformation,[],[f13])).
% 11.85/1.99  
% 11.85/1.99  fof(f49,plain,(
% 11.85/1.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 11.85/1.99    inference(flattening,[],[f48])).
% 11.85/1.99  
% 11.85/1.99  fof(f76,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f49])).
% 11.85/1.99  
% 11.85/1.99  fof(f131,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.85/1.99    inference(definition_unfolding,[],[f76,f122,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f17,axiom,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f32,plain,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 11.85/1.99    inference(ennf_transformation,[],[f17])).
% 11.85/1.99  
% 11.85/1.99  fof(f44,plain,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 11.85/1.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 11.85/1.99  
% 11.85/1.99  fof(f43,plain,(
% 11.85/1.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 11.85/1.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.85/1.99  
% 11.85/1.99  fof(f45,plain,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 11.85/1.99    inference(definition_folding,[],[f32,f44,f43])).
% 11.85/1.99  
% 11.85/1.99  fof(f58,plain,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 11.85/1.99    inference(nnf_transformation,[],[f45])).
% 11.85/1.99  
% 11.85/1.99  fof(f98,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 11.85/1.99    inference(cnf_transformation,[],[f58])).
% 11.85/1.99  
% 11.85/1.99  fof(f149,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 11.85/1.99    inference(equality_resolution,[],[f98])).
% 11.85/1.99  
% 11.85/1.99  fof(f51,plain,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 11.85/1.99    inference(nnf_transformation,[],[f44])).
% 11.85/1.99  
% 11.85/1.99  fof(f52,plain,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 11.85/1.99    inference(rectify,[],[f51])).
% 11.85/1.99  
% 11.85/1.99  fof(f53,plain,(
% 11.85/1.99    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 11.85/1.99    introduced(choice_axiom,[])).
% 11.85/1.99  
% 11.85/1.99  fof(f54,plain,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 11.85/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).
% 11.85/1.99  
% 11.85/1.99  fof(f85,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f54])).
% 11.85/1.99  
% 11.85/1.99  fof(f55,plain,(
% 11.85/1.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 11.85/1.99    inference(nnf_transformation,[],[f43])).
% 11.85/1.99  
% 11.85/1.99  fof(f56,plain,(
% 11.85/1.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 11.85/1.99    inference(flattening,[],[f55])).
% 11.85/1.99  
% 11.85/1.99  fof(f57,plain,(
% 11.85/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 11.85/1.99    inference(rectify,[],[f56])).
% 11.85/1.99  
% 11.85/1.99  fof(f89,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f57])).
% 11.85/1.99  
% 11.85/1.99  fof(f78,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 11.85/1.99    inference(cnf_transformation,[],[f49])).
% 11.85/1.99  
% 11.85/1.99  fof(f129,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 11.85/1.99    inference(definition_unfolding,[],[f78,f122,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f139,plain,(
% 11.85/1.99    ( ! [X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 11.85/1.99    inference(equality_resolution,[],[f129])).
% 11.85/1.99  
% 11.85/1.99  fof(f71,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f46])).
% 11.85/1.99  
% 11.85/1.99  fof(f125,plain,(
% 11.85/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f71,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f109,plain,(
% 11.85/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f59])).
% 11.85/1.99  
% 11.85/1.99  fof(f96,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X2) )),
% 11.85/1.99    inference(cnf_transformation,[],[f57])).
% 11.85/1.99  
% 11.85/1.99  fof(f142,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X2,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 11.85/1.99    inference(equality_resolution,[],[f96])).
% 11.85/1.99  
% 11.85/1.99  fof(f12,axiom,(
% 11.85/1.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f47,plain,(
% 11.85/1.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.85/1.99    inference(nnf_transformation,[],[f12])).
% 11.85/1.99  
% 11.85/1.99  fof(f74,plain,(
% 11.85/1.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.85/1.99    inference(cnf_transformation,[],[f47])).
% 11.85/1.99  
% 11.85/1.99  fof(f1,axiom,(
% 11.85/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f62,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f1])).
% 11.85/1.99  
% 11.85/1.99  fof(f25,axiom,(
% 11.85/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f107,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.85/1.99    inference(cnf_transformation,[],[f25])).
% 11.85/1.99  
% 11.85/1.99  fof(f120,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.85/1.99    inference(definition_unfolding,[],[f107,f119])).
% 11.85/1.99  
% 11.85/1.99  fof(f121,plain,(
% 11.85/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.85/1.99    inference(definition_unfolding,[],[f62,f120])).
% 11.85/1.99  
% 11.85/1.99  fof(f128,plain,(
% 11.85/1.99    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.85/1.99    inference(definition_unfolding,[],[f74,f121,f122,f122,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f138,plain,(
% 11.85/1.99    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 11.85/1.99    inference(equality_resolution,[],[f128])).
% 11.85/1.99  
% 11.85/1.99  fof(f2,axiom,(
% 11.85/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f63,plain,(
% 11.85/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.85/1.99    inference(cnf_transformation,[],[f2])).
% 11.85/1.99  
% 11.85/1.99  fof(f24,axiom,(
% 11.85/1.99    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 11.85/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/1.99  
% 11.85/1.99  fof(f106,plain,(
% 11.85/1.99    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 11.85/1.99    inference(cnf_transformation,[],[f24])).
% 11.85/1.99  
% 11.85/1.99  fof(f135,plain,(
% 11.85/1.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 11.85/1.99    inference(definition_unfolding,[],[f106,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f114,plain,(
% 11.85/1.99    k1_tarski(k1_xboole_0) != k7_setfam_1(sK3,sK4)),
% 11.85/1.99    inference(cnf_transformation,[],[f61])).
% 11.85/1.99  
% 11.85/1.99  fof(f136,plain,(
% 11.85/1.99    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4)),
% 11.85/1.99    inference(definition_unfolding,[],[f114,f122])).
% 11.85/1.99  
% 11.85/1.99  fof(f90,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 11.85/1.99    inference(cnf_transformation,[],[f57])).
% 11.85/1.99  
% 11.85/1.99  fof(f148,plain,(
% 11.85/1.99    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 11.85/1.99    inference(equality_resolution,[],[f90])).
% 11.85/1.99  
% 11.85/1.99  cnf(c_3,plain,
% 11.85/1.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 11.85/1.99      inference(cnf_transformation,[],[f126]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_31,plain,
% 11.85/1.99      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 11.85/1.99      | ~ r2_hidden(X0,X1) ),
% 11.85/1.99      inference(cnf_transformation,[],[f134]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1772,plain,
% 11.85/1.99      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 11.85/1.99      | r2_hidden(X0,X1) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6155,plain,
% 11.85/1.99      ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 11.85/1.99      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_3,c_1772]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_13,plain,
% 11.85/1.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f132]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_36,plain,
% 11.85/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.85/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.85/1.99      | ~ r2_hidden(X0,X2)
% 11.85/1.99      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f110]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1768,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.85/1.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.85/1.99      | r2_hidden(X0,X2) != iProver_top
% 11.85/1.99      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_4684,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.85/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 11.85/1.99      | r2_hidden(X1,k7_setfam_1(X1,X0)) = iProver_top
% 11.85/1.99      | r2_hidden(k1_xboole_0,X0) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_13,c_1768]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_9623,plain,
% 11.85/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 11.85/1.99      | r2_hidden(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))) = iProver_top
% 11.85/1.99      | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 11.85/1.99      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_6155,c_4684]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_30,plain,
% 11.85/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_65,plain,
% 11.85/1.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_67,plain,
% 11.85/1.99      ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_65]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_29,plain,
% 11.85/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f133]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_68,plain,
% 11.85/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1774,plain,
% 11.85/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_12,plain,
% 11.85/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.85/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1790,plain,
% 11.85/1.99      ( m1_subset_1(X0,X1) != iProver_top
% 11.85/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.85/1.99      | v1_xboole_0(X1) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_4694,plain,
% 11.85/1.99      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top
% 11.85/1.99      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1774,c_1790]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_4697,plain,
% 11.85/1.99      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.85/1.99      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_4694]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_33361,plain,
% 11.85/1.99      ( r2_hidden(X0,k7_setfam_1(X0,k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
% 11.85/1.99      inference(global_propositional_subsumption,
% 11.85/1.99                [status(thm)],
% 11.85/1.99                [c_9623,c_65,c_67,c_68,c_4694,c_4697]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_40,negated_conjecture,
% 11.85/1.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
% 11.85/1.99      inference(cnf_transformation,[],[f137]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1,plain,
% 11.85/1.99      ( ~ r2_hidden(X0,X1)
% 11.85/1.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.85/1.99      inference(cnf_transformation,[],[f124]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1798,plain,
% 11.85/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.85/1.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7834,plain,
% 11.85/1.99      ( r2_hidden(sK3,X0) != iProver_top
% 11.85/1.99      | r1_tarski(sK4,X0) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_40,c_1798]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_33369,plain,
% 11.85/1.99      ( r1_tarski(sK4,k7_setfam_1(sK3,k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_33361,c_7834]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_41,negated_conjecture,
% 11.85/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 11.85/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1765,plain,
% 11.85/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_33,plain,
% 11.85/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.85/1.99      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1770,plain,
% 11.85/1.99      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 11.85/1.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_4537,plain,
% 11.85/1.99      ( k7_setfam_1(sK3,k7_setfam_1(sK3,sK4)) = sK4 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1765,c_1770]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_38,plain,
% 11.85/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.85/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.85/1.99      | r1_tarski(X0,X2)
% 11.85/1.99      | ~ r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f111]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1766,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.85/1.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.85/1.99      | r1_tarski(X0,X2) = iProver_top
% 11.85/1.99      | r1_tarski(k7_setfam_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_4539,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 11.85/1.99      | m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 11.85/1.99      | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
% 11.85/1.99      | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_4537,c_1766]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_42,plain,
% 11.85/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_32,plain,
% 11.85/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.85/1.99      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 11.85/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2544,plain,
% 11.85/1.99      ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3)))
% 11.85/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_32]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2545,plain,
% 11.85/1.99      ( m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top
% 11.85/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_2544]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5159,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 11.85/1.99      | r1_tarski(k7_setfam_1(sK3,sK4),X0) = iProver_top
% 11.85/1.99      | r1_tarski(sK4,k7_setfam_1(sK3,X0)) != iProver_top ),
% 11.85/1.99      inference(global_propositional_subsumption,
% 11.85/1.99                [status(thm)],
% 11.85/1.99                [c_4539,c_42,c_2545]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_33375,plain,
% 11.85/1.99      ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 11.85/1.99      | r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_33369,c_5159]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_34010,plain,
% 11.85/1.99      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 11.85/1.99      | r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_6155,c_33375]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7785,plain,
% 11.85/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_29]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_7786,plain,
% 11.85/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_7785]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_17978,plain,
% 11.85/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 11.85/1.99      | r2_hidden(X0,k1_zfmisc_1(sK3))
% 11.85/1.99      | v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_17982,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 11.85/1.99      | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
% 11.85/1.99      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_17978]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_17984,plain,
% 11.85/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 11.85/1.99      | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top
% 11.85/1.99      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_17982]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_24918,plain,
% 11.85/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_30]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_24919,plain,
% 11.85/1.99      ( v1_xboole_0(k1_zfmisc_1(sK3)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_24918]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_34013,plain,
% 11.85/1.99      ( r1_tarski(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.85/1.99      inference(global_propositional_subsumption,
% 11.85/1.99                [status(thm)],
% 11.85/1.99                [c_34010,c_7786,c_17984,c_24919]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_8,plain,
% 11.85/1.99      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 11.85/1.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 11.85/1.99      | k1_xboole_0 = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f131]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1794,plain,
% 11.85/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 11.85/1.99      | k1_xboole_0 = X1
% 11.85/1.99      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_8975,plain,
% 11.85/1.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = X0
% 11.85/1.99      | k1_xboole_0 = X0
% 11.85/1.99      | r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_3,c_1794]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_8978,plain,
% 11.85/1.99      ( k1_zfmisc_1(k1_xboole_0) = X0
% 11.85/1.99      | k1_xboole_0 = X0
% 11.85/1.99      | r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_8975,c_3]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_34017,plain,
% 11.85/1.99      ( k7_setfam_1(sK3,sK4) = k1_zfmisc_1(k1_xboole_0)
% 11.85/1.99      | k7_setfam_1(sK3,sK4) = k1_xboole_0 ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_34013,c_8978]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6158,plain,
% 11.85/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.85/1.99      | r2_hidden(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 11.85/1.99      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_1772,c_1790]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_28,plain,
% 11.85/1.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f149]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1775,plain,
% 11.85/1.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5728,plain,
% 11.85/1.99      ( sP1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_3,c_1775]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_17,plain,
% 11.85/1.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 11.85/1.99      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 11.85/1.99      | ~ r2_hidden(X0,X9) ),
% 11.85/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1786,plain,
% 11.85/1.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) = iProver_top
% 11.85/1.99      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 11.85/1.99      | r2_hidden(X0,X9) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_9752,plain,
% 11.85/1.99      ( sP0(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 11.85/1.99      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_5728,c_1786]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_26,plain,
% 11.85/1.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 11.85/1.99      | X1 = X0
% 11.85/1.99      | X8 = X0
% 11.85/1.99      | X7 = X0
% 11.85/1.99      | X6 = X0
% 11.85/1.99      | X5 = X0
% 11.85/1.99      | X4 = X0
% 11.85/1.99      | X3 = X0
% 11.85/1.99      | X2 = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1777,plain,
% 11.85/1.99      ( X0 = X1
% 11.85/1.99      | X2 = X1
% 11.85/1.99      | X3 = X1
% 11.85/1.99      | X4 = X1
% 11.85/1.99      | X5 = X1
% 11.85/1.99      | X6 = X1
% 11.85/1.99      | X7 = X1
% 11.85/1.99      | X8 = X1
% 11.85/1.99      | sP0(X1,X0,X8,X7,X6,X5,X4,X3,X2) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_23553,plain,
% 11.85/1.99      ( k1_xboole_0 = X0
% 11.85/1.99      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_9752,c_1777]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_23562,plain,
% 11.85/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 11.85/1.99      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 11.85/1.99      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_6158,c_23553]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_23571,plain,
% 11.85/1.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 11.85/1.99      | r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top
% 11.85/1.99      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_23562]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1010,plain,
% 11.85/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.85/1.99      theory(equality) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_21773,plain,
% 11.85/1.99      ( r2_hidden(X0,X1)
% 11.85/1.99      | ~ r2_hidden(X2,k7_setfam_1(sK3,sK4))
% 11.85/1.99      | X0 != X2
% 11.85/1.99      | X1 != k7_setfam_1(sK3,sK4) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1010]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_21779,plain,
% 11.85/1.99      ( X0 != X1
% 11.85/1.99      | X2 != k7_setfam_1(sK3,sK4)
% 11.85/1.99      | r2_hidden(X0,X2) = iProver_top
% 11.85/1.99      | r2_hidden(X1,k7_setfam_1(sK3,sK4)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_21773]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_21781,plain,
% 11.85/1.99      ( k1_xboole_0 != k7_setfam_1(sK3,sK4)
% 11.85/1.99      | k1_xboole_0 != k1_xboole_0
% 11.85/1.99      | r2_hidden(k1_xboole_0,k7_setfam_1(sK3,sK4)) != iProver_top
% 11.85/1.99      | r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_21779]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6,plain,
% 11.85/1.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f139]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1796,plain,
% 11.85/1.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_9018,plain,
% 11.85/1.99      ( r1_tarski(sK4,sK4) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_40,c_1796]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2,plain,
% 11.85/1.99      ( r2_hidden(X0,X1)
% 11.85/1.99      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.85/1.99      inference(cnf_transformation,[],[f125]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1797,plain,
% 11.85/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.85/1.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_6290,plain,
% 11.85/1.99      ( r2_hidden(sK3,X0) = iProver_top
% 11.85/1.99      | r1_tarski(sK4,X0) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_40,c_1797]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_9027,plain,
% 11.85/1.99      ( r2_hidden(sK3,sK4) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_9018,c_6290]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_37,plain,
% 11.85/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.85/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.85/1.99      | r2_hidden(X0,X2)
% 11.85/1.99      | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 11.85/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1767,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.85/1.99      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 11.85/1.99      | r2_hidden(X0,X2) = iProver_top
% 11.85/1.99      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_4540,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 11.85/1.99      | m1_subset_1(k7_setfam_1(sK3,sK4),k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top
% 11.85/1.99      | r2_hidden(X0,k7_setfam_1(sK3,sK4)) = iProver_top
% 11.85/1.99      | r2_hidden(k3_subset_1(sK3,X0),sK4) != iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_4537,c_1767]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5035,plain,
% 11.85/1.99      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 11.85/1.99      | r2_hidden(X0,k7_setfam_1(sK3,sK4)) = iProver_top
% 11.85/1.99      | r2_hidden(k3_subset_1(sK3,X0),sK4) != iProver_top ),
% 11.85/1.99      inference(global_propositional_subsumption,
% 11.85/1.99                [status(thm)],
% 11.85/1.99                [c_4540,c_42,c_2545]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5041,plain,
% 11.85/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 11.85/1.99      | r2_hidden(sK3,sK4) != iProver_top
% 11.85/1.99      | r2_hidden(k1_xboole_0,k7_setfam_1(sK3,sK4)) = iProver_top ),
% 11.85/1.99      inference(superposition,[status(thm)],[c_13,c_5035]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_19,plain,
% 11.85/1.99      ( sP0(X0,X1,X0,X2,X3,X4,X5,X6,X7) ),
% 11.85/1.99      inference(cnf_transformation,[],[f142]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2133,plain,
% 11.85/1.99      ( sP0(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0,X1,X2,X3,X4,X5,X6) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2134,plain,
% 11.85/1.99      ( sP0(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0,X1,X2,X3,X4,X5,X6) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_2133]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_2136,plain,
% 11.85/1.99      ( sP0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_2134]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1017,plain,
% 11.85/1.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 11.85/1.99      | sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8)
% 11.85/1.99      | X9 != X0 ),
% 11.85/1.99      theory(equality) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1906,plain,
% 11.85/1.99      ( ~ sP0(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1,X2,X3,X4,X5,X6,X7)
% 11.85/1.99      | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1,X2,X3,X4,X5,X6,X7)
% 11.85/1.99      | k7_setfam_1(sK3,sK4) != X0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1017]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1907,plain,
% 11.85/1.99      ( k7_setfam_1(sK3,sK4) != X0
% 11.85/1.99      | sP0(X0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1,X2,X3,X4,X5,X6,X7) != iProver_top
% 11.85/1.99      | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_1906]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1909,plain,
% 11.85/1.99      ( k7_setfam_1(sK3,sK4) != k1_xboole_0
% 11.85/1.99      | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 11.85/1.99      | sP0(k1_xboole_0,k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1907]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1838,plain,
% 11.85/1.99      ( ~ sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X0,X1,X2,X3,X4,X5,X6)
% 11.85/1.99      | X6 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X5 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X4 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X3 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X2 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X1 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X0 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k7_setfam_1(sK3,sK4) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_26]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1839,plain,
% 11.85/1.99      ( X0 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X1 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X2 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X3 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X4 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X5 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | X6 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),X6,X5,X4,X3,X2,X1,X0) != iProver_top ),
% 11.85/1.99      inference(predicate_to_equality,[status(thm)],[c_1838]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1841,plain,
% 11.85/1.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | k1_xboole_0 = k7_setfam_1(sK3,sK4)
% 11.85/1.99      | sP0(k7_setfam_1(sK3,sK4),k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1839]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_5,plain,
% 11.85/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.85/1.99      inference(cnf_transformation,[],[f138]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_0,plain,
% 11.85/1.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_34,plain,
% 11.85/1.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 11.85/1.99      inference(cnf_transformation,[],[f135]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1800,plain,
% 11.85/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 11.85/1.99      inference(demodulation,[status(thm)],[c_5,c_0,c_34]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1820,plain,
% 11.85/1.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_1800]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_39,negated_conjecture,
% 11.85/1.99      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k7_setfam_1(sK3,sK4) ),
% 11.85/1.99      inference(cnf_transformation,[],[f136]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_1799,plain,
% 11.85/1.99      ( k7_setfam_1(sK3,sK4) != k1_zfmisc_1(k1_xboole_0) ),
% 11.85/1.99      inference(light_normalisation,[status(thm)],[c_39,c_3]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_25,plain,
% 11.85/1.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 11.85/1.99      inference(cnf_transformation,[],[f148]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_81,plain,
% 11.85/1.99      ( sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_25]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(c_78,plain,
% 11.85/1.99      ( ~ sP0(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 11.85/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.85/1.99      inference(instantiation,[status(thm)],[c_26]) ).
% 11.85/1.99  
% 11.85/1.99  cnf(contradiction,plain,
% 11.85/1.99      ( $false ),
% 11.85/1.99      inference(minisat,
% 11.85/1.99                [status(thm)],
% 11.85/1.99                [c_34017,c_23571,c_21781,c_9027,c_7786,c_5041,c_2136,
% 11.85/1.99                 c_1909,c_1841,c_1820,c_1799,c_81,c_78,c_67,c_39]) ).
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.85/1.99  
% 11.85/1.99  ------                               Statistics
% 11.85/1.99  
% 11.85/1.99  ------ General
% 11.85/1.99  
% 11.85/1.99  abstr_ref_over_cycles:                  0
% 11.85/1.99  abstr_ref_under_cycles:                 0
% 11.85/1.99  gc_basic_clause_elim:                   0
% 11.85/1.99  forced_gc_time:                         0
% 11.85/1.99  parsing_time:                           0.007
% 11.85/1.99  unif_index_cands_time:                  0.
% 11.85/1.99  unif_index_add_time:                    0.
% 11.85/1.99  orderings_time:                         0.
% 11.85/1.99  out_proof_time:                         0.014
% 11.85/1.99  total_time:                             1.502
% 11.85/1.99  num_of_symbols:                         47
% 11.85/1.99  num_of_terms:                           34322
% 11.85/1.99  
% 11.85/1.99  ------ Preprocessing
% 11.85/1.99  
% 11.85/1.99  num_of_splits:                          0
% 11.85/1.99  num_of_split_atoms:                     0
% 11.85/1.99  num_of_reused_defs:                     0
% 11.85/1.99  num_eq_ax_congr_red:                    52
% 11.85/1.99  num_of_sem_filtered_clauses:            1
% 11.85/1.99  num_of_subtypes:                        0
% 11.85/1.99  monotx_restored_types:                  0
% 11.85/1.99  sat_num_of_epr_types:                   0
% 11.85/1.99  sat_num_of_non_cyclic_types:            0
% 11.85/1.99  sat_guarded_non_collapsed_types:        0
% 11.85/1.99  num_pure_diseq_elim:                    0
% 11.85/1.99  simp_replaced_by:                       0
% 11.85/1.99  res_preprocessed:                       155
% 11.85/1.99  prep_upred:                             0
% 11.85/1.99  prep_unflattend:                        298
% 11.85/1.99  smt_new_axioms:                         0
% 11.85/1.99  pred_elim_cands:                        6
% 11.85/1.99  pred_elim:                              0
% 11.85/1.99  pred_elim_cl:                           0
% 11.85/1.99  pred_elim_cycles:                       2
% 11.85/1.99  merged_defs:                            6
% 11.85/1.99  merged_defs_ncl:                        0
% 11.85/1.99  bin_hyper_res:                          6
% 11.85/1.99  prep_cycles:                            3
% 11.85/1.99  pred_elim_time:                         0.008
% 11.85/1.99  splitting_time:                         0.
% 11.85/1.99  sem_filter_time:                        0.
% 11.85/1.99  monotx_time:                            0.
% 11.85/1.99  subtype_inf_time:                       0.
% 11.85/1.99  
% 11.85/1.99  ------ Problem properties
% 11.85/1.99  
% 11.85/1.99  clauses:                                42
% 11.85/1.99  conjectures:                            3
% 11.85/1.99  epr:                                    15
% 11.85/1.99  horn:                                   36
% 11.85/1.99  ground:                                 4
% 11.85/1.99  unary:                                  21
% 11.85/1.99  binary:                                 7
% 11.85/1.99  lits:                                   86
% 11.85/1.99  lits_eq:                                23
% 11.85/1.99  fd_pure:                                0
% 11.85/1.99  fd_pseudo:                              0
% 11.85/1.99  fd_cond:                                1
% 11.85/1.99  fd_pseudo_cond:                         4
% 11.85/1.99  ac_symbols:                             0
% 11.85/1.99  
% 11.85/1.99  ------ Propositional Solver
% 11.85/1.99  
% 11.85/1.99  prop_solver_calls:                      28
% 11.85/1.99  prop_fast_solver_calls:                 1718
% 11.85/1.99  smt_solver_calls:                       0
% 11.85/1.99  smt_fast_solver_calls:                  0
% 11.85/1.99  prop_num_of_clauses:                    10139
% 11.85/1.99  prop_preprocess_simplified:             22469
% 11.85/1.99  prop_fo_subsumed:                       42
% 11.85/1.99  prop_solver_time:                       0.
% 11.85/1.99  smt_solver_time:                        0.
% 11.85/1.99  smt_fast_solver_time:                   0.
% 11.85/1.99  prop_fast_solver_time:                  0.
% 11.85/1.99  prop_unsat_core_time:                   0.001
% 11.85/1.99  
% 11.85/1.99  ------ QBF
% 11.85/1.99  
% 11.85/1.99  qbf_q_res:                              0
% 11.85/1.99  qbf_num_tautologies:                    0
% 11.85/1.99  qbf_prep_cycles:                        0
% 11.85/1.99  
% 11.85/1.99  ------ BMC1
% 11.85/1.99  
% 11.85/1.99  bmc1_current_bound:                     -1
% 11.85/1.99  bmc1_last_solved_bound:                 -1
% 11.85/1.99  bmc1_unsat_core_size:                   -1
% 11.85/1.99  bmc1_unsat_core_parents_size:           -1
% 11.85/1.99  bmc1_merge_next_fun:                    0
% 11.85/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.85/1.99  
% 11.85/1.99  ------ Instantiation
% 11.85/1.99  
% 11.85/1.99  inst_num_of_clauses:                    2678
% 11.85/1.99  inst_num_in_passive:                    783
% 11.85/1.99  inst_num_in_active:                     863
% 11.85/1.99  inst_num_in_unprocessed:                1032
% 11.85/1.99  inst_num_of_loops:                      1440
% 11.85/1.99  inst_num_of_learning_restarts:          0
% 11.85/1.99  inst_num_moves_active_passive:          576
% 11.85/1.99  inst_lit_activity:                      0
% 11.85/1.99  inst_lit_activity_moves:                1
% 11.85/1.99  inst_num_tautologies:                   0
% 11.85/1.99  inst_num_prop_implied:                  0
% 11.85/1.99  inst_num_existing_simplified:           0
% 11.85/1.99  inst_num_eq_res_simplified:             0
% 11.85/1.99  inst_num_child_elim:                    0
% 11.85/1.99  inst_num_of_dismatching_blockings:      3638
% 11.85/1.99  inst_num_of_non_proper_insts:           4578
% 11.85/1.99  inst_num_of_duplicates:                 0
% 11.85/1.99  inst_inst_num_from_inst_to_res:         0
% 11.85/1.99  inst_dismatching_checking_time:         0.
% 11.85/1.99  
% 11.85/1.99  ------ Resolution
% 11.85/1.99  
% 11.85/1.99  res_num_of_clauses:                     0
% 11.85/1.99  res_num_in_passive:                     0
% 11.85/1.99  res_num_in_active:                      0
% 11.85/1.99  res_num_of_loops:                       158
% 11.85/1.99  res_forward_subset_subsumed:            3669
% 11.85/1.99  res_backward_subset_subsumed:           0
% 11.85/1.99  res_forward_subsumed:                   0
% 11.85/1.99  res_backward_subsumed:                  0
% 11.85/1.99  res_forward_subsumption_resolution:     0
% 11.85/1.99  res_backward_subsumption_resolution:    0
% 11.85/1.99  res_clause_to_clause_subsumption:       3292
% 11.85/1.99  res_orphan_elimination:                 0
% 11.85/1.99  res_tautology_del:                      1994
% 11.85/1.99  res_num_eq_res_simplified:              0
% 11.85/1.99  res_num_sel_changes:                    0
% 11.85/1.99  res_moves_from_active_to_pass:          0
% 11.85/1.99  
% 11.85/1.99  ------ Superposition
% 11.85/1.99  
% 11.85/1.99  sup_time_total:                         0.
% 11.85/1.99  sup_time_generating:                    0.
% 11.85/1.99  sup_time_sim_full:                      0.
% 11.85/1.99  sup_time_sim_immed:                     0.
% 11.85/1.99  
% 11.85/1.99  sup_num_of_clauses:                     435
% 11.85/1.99  sup_num_in_active:                      267
% 11.85/1.99  sup_num_in_passive:                     168
% 11.85/1.99  sup_num_of_loops:                       287
% 11.85/1.99  sup_fw_superposition:                   574
% 11.85/1.99  sup_bw_superposition:                   353
% 11.85/1.99  sup_immediate_simplified:               212
% 11.85/1.99  sup_given_eliminated:                   1
% 11.85/1.99  comparisons_done:                       0
% 11.85/1.99  comparisons_avoided:                    50
% 11.85/1.99  
% 11.85/1.99  ------ Simplifications
% 11.85/1.99  
% 11.85/1.99  
% 11.85/1.99  sim_fw_subset_subsumed:                 45
% 11.85/1.99  sim_bw_subset_subsumed:                 3
% 11.85/1.99  sim_fw_subsumed:                        116
% 11.85/1.99  sim_bw_subsumed:                        16
% 11.85/1.99  sim_fw_subsumption_res:                 0
% 11.85/1.99  sim_bw_subsumption_res:                 0
% 11.85/1.99  sim_tautology_del:                      67
% 11.85/1.99  sim_eq_tautology_del:                   43
% 11.85/1.99  sim_eq_res_simp:                        0
% 11.85/1.99  sim_fw_demodulated:                     30
% 11.85/1.99  sim_bw_demodulated:                     4
% 11.85/1.99  sim_light_normalised:                   35
% 11.85/1.99  sim_joinable_taut:                      0
% 11.85/1.99  sim_joinable_simp:                      0
% 11.85/1.99  sim_ac_normalised:                      0
% 11.85/1.99  sim_smt_subsumption:                    0
% 11.85/1.99  
%------------------------------------------------------------------------------

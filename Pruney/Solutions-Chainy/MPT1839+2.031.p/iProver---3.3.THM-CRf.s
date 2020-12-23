%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:46 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 274 expanded)
%              Number of clauses        :   35 (  36 expanded)
%              Number of leaves         :   18 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  289 ( 688 expanded)
%              Number of equality atoms :   86 ( 235 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f83])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f64,f84])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK5)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK4,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK4,X1)) )
      & v1_zfmisc_1(sK4)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r1_tarski(sK4,sK5)
    & ~ v1_xboole_0(k3_xboole_0(sK4,sK5))
    & v1_zfmisc_1(sK4)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f46,f45])).

fof(f76,plain,(
    v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))) ),
    inference(definition_unfolding,[],[f77,f84])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f63,f84])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f55,f85])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f84])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f54,f85])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f53,f85])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ~ r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1289,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1278,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,negated_conjecture,
    ( v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 = X0 ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_246,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK4)
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_22])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0)
    | sK4 = X0 ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_1272,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_2133,plain,
    ( k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) = sK4
    | v1_xboole_0(k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1272])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1274,plain,
    ( v1_xboole_0(k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2364,plain,
    ( k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
    inference(superposition,[status(thm)],[c_2133,c_1274])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1284,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3856,plain,
    ( r2_hidden(X0,k5_xboole_0(sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_1284])).

cnf(c_12,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1283,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3813,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1283])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1282,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2916,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1282])).

cnf(c_4072,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3813,c_2916])).

cnf(c_4895,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3856,c_4072])).

cnf(c_4898,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | r2_hidden(sK1(sK4,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_4895])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1290,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5087,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4898,c_1290])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,plain,
    ( r1_tarski(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5087,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n019.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 20:12:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.68/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/0.97  
% 2.68/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.68/0.97  
% 2.68/0.97  ------  iProver source info
% 2.68/0.97  
% 2.68/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.68/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.68/0.97  git: non_committed_changes: false
% 2.68/0.97  git: last_make_outside_of_git: false
% 2.68/0.97  
% 2.68/0.97  ------ 
% 2.68/0.97  
% 2.68/0.97  ------ Input Options
% 2.68/0.97  
% 2.68/0.97  --out_options                           all
% 2.68/0.97  --tptp_safe_out                         true
% 2.68/0.97  --problem_path                          ""
% 2.68/0.97  --include_path                          ""
% 2.68/0.97  --clausifier                            res/vclausify_rel
% 2.68/0.97  --clausifier_options                    --mode clausify
% 2.68/0.97  --stdin                                 false
% 2.68/0.97  --stats_out                             all
% 2.68/0.97  
% 2.68/0.97  ------ General Options
% 2.68/0.97  
% 2.68/0.97  --fof                                   false
% 2.68/0.97  --time_out_real                         305.
% 2.68/0.97  --time_out_virtual                      -1.
% 2.68/0.97  --symbol_type_check                     false
% 2.68/0.97  --clausify_out                          false
% 2.68/0.97  --sig_cnt_out                           false
% 2.68/0.97  --trig_cnt_out                          false
% 2.68/0.97  --trig_cnt_out_tolerance                1.
% 2.68/0.97  --trig_cnt_out_sk_spl                   false
% 2.68/0.97  --abstr_cl_out                          false
% 2.68/0.97  
% 2.68/0.97  ------ Global Options
% 2.68/0.97  
% 2.68/0.97  --schedule                              default
% 2.68/0.97  --add_important_lit                     false
% 2.68/0.97  --prop_solver_per_cl                    1000
% 2.68/0.97  --min_unsat_core                        false
% 2.68/0.97  --soft_assumptions                      false
% 2.68/0.97  --soft_lemma_size                       3
% 2.68/0.97  --prop_impl_unit_size                   0
% 2.68/0.97  --prop_impl_unit                        []
% 2.68/0.97  --share_sel_clauses                     true
% 2.68/0.97  --reset_solvers                         false
% 2.68/0.97  --bc_imp_inh                            [conj_cone]
% 2.68/0.97  --conj_cone_tolerance                   3.
% 2.68/0.97  --extra_neg_conj                        none
% 2.68/0.97  --large_theory_mode                     true
% 2.68/0.97  --prolific_symb_bound                   200
% 2.68/0.97  --lt_threshold                          2000
% 2.68/0.97  --clause_weak_htbl                      true
% 2.68/0.97  --gc_record_bc_elim                     false
% 2.68/0.97  
% 2.68/0.97  ------ Preprocessing Options
% 2.68/0.97  
% 2.68/0.97  --preprocessing_flag                    true
% 2.68/0.97  --time_out_prep_mult                    0.1
% 2.68/0.97  --splitting_mode                        input
% 2.68/0.97  --splitting_grd                         true
% 2.68/0.97  --splitting_cvd                         false
% 2.68/0.97  --splitting_cvd_svl                     false
% 2.68/0.97  --splitting_nvd                         32
% 2.68/0.97  --sub_typing                            true
% 2.68/0.97  --prep_gs_sim                           true
% 2.68/0.97  --prep_unflatten                        true
% 2.68/0.97  --prep_res_sim                          true
% 2.68/0.97  --prep_upred                            true
% 2.68/0.97  --prep_sem_filter                       exhaustive
% 2.68/0.97  --prep_sem_filter_out                   false
% 2.68/0.97  --pred_elim                             true
% 2.68/0.97  --res_sim_input                         true
% 2.68/0.97  --eq_ax_congr_red                       true
% 2.68/0.97  --pure_diseq_elim                       true
% 2.68/0.97  --brand_transform                       false
% 2.68/0.97  --non_eq_to_eq                          false
% 2.68/0.97  --prep_def_merge                        true
% 2.68/0.97  --prep_def_merge_prop_impl              false
% 2.68/0.97  --prep_def_merge_mbd                    true
% 2.68/0.97  --prep_def_merge_tr_red                 false
% 2.68/0.97  --prep_def_merge_tr_cl                  false
% 2.68/0.97  --smt_preprocessing                     true
% 2.68/0.97  --smt_ac_axioms                         fast
% 2.68/0.97  --preprocessed_out                      false
% 2.68/0.97  --preprocessed_stats                    false
% 2.68/0.97  
% 2.68/0.97  ------ Abstraction refinement Options
% 2.68/0.97  
% 2.68/0.97  --abstr_ref                             []
% 2.68/0.97  --abstr_ref_prep                        false
% 2.68/0.97  --abstr_ref_until_sat                   false
% 2.68/0.97  --abstr_ref_sig_restrict                funpre
% 2.68/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/0.97  --abstr_ref_under                       []
% 2.68/0.97  
% 2.68/0.97  ------ SAT Options
% 2.68/0.97  
% 2.68/0.97  --sat_mode                              false
% 2.68/0.97  --sat_fm_restart_options                ""
% 2.68/0.97  --sat_gr_def                            false
% 2.68/0.97  --sat_epr_types                         true
% 2.68/0.97  --sat_non_cyclic_types                  false
% 2.68/0.97  --sat_finite_models                     false
% 2.68/0.97  --sat_fm_lemmas                         false
% 2.68/0.97  --sat_fm_prep                           false
% 2.68/0.97  --sat_fm_uc_incr                        true
% 2.68/0.97  --sat_out_model                         small
% 2.68/0.97  --sat_out_clauses                       false
% 2.68/0.97  
% 2.68/0.97  ------ QBF Options
% 2.68/0.97  
% 2.68/0.97  --qbf_mode                              false
% 2.68/0.97  --qbf_elim_univ                         false
% 2.68/0.97  --qbf_dom_inst                          none
% 2.68/0.97  --qbf_dom_pre_inst                      false
% 2.68/0.97  --qbf_sk_in                             false
% 2.68/0.97  --qbf_pred_elim                         true
% 2.68/0.97  --qbf_split                             512
% 2.68/0.97  
% 2.68/0.97  ------ BMC1 Options
% 2.68/0.97  
% 2.68/0.97  --bmc1_incremental                      false
% 2.68/0.97  --bmc1_axioms                           reachable_all
% 2.68/0.97  --bmc1_min_bound                        0
% 2.68/0.97  --bmc1_max_bound                        -1
% 2.68/0.97  --bmc1_max_bound_default                -1
% 2.68/0.97  --bmc1_symbol_reachability              true
% 2.68/0.97  --bmc1_property_lemmas                  false
% 2.68/0.97  --bmc1_k_induction                      false
% 2.68/0.97  --bmc1_non_equiv_states                 false
% 2.68/0.97  --bmc1_deadlock                         false
% 2.68/0.97  --bmc1_ucm                              false
% 2.68/0.97  --bmc1_add_unsat_core                   none
% 2.68/0.97  --bmc1_unsat_core_children              false
% 2.68/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/0.97  --bmc1_out_stat                         full
% 2.68/0.97  --bmc1_ground_init                      false
% 2.68/0.97  --bmc1_pre_inst_next_state              false
% 2.68/0.97  --bmc1_pre_inst_state                   false
% 2.68/0.97  --bmc1_pre_inst_reach_state             false
% 2.68/0.97  --bmc1_out_unsat_core                   false
% 2.68/0.97  --bmc1_aig_witness_out                  false
% 2.68/0.97  --bmc1_verbose                          false
% 2.68/0.97  --bmc1_dump_clauses_tptp                false
% 2.68/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.68/0.97  --bmc1_dump_file                        -
% 2.68/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.68/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.68/0.97  --bmc1_ucm_extend_mode                  1
% 2.68/0.97  --bmc1_ucm_init_mode                    2
% 2.68/0.97  --bmc1_ucm_cone_mode                    none
% 2.68/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.68/0.97  --bmc1_ucm_relax_model                  4
% 2.68/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.68/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/0.97  --bmc1_ucm_layered_model                none
% 2.68/0.97  --bmc1_ucm_max_lemma_size               10
% 2.68/0.97  
% 2.68/0.97  ------ AIG Options
% 2.68/0.97  
% 2.68/0.97  --aig_mode                              false
% 2.68/0.97  
% 2.68/0.97  ------ Instantiation Options
% 2.68/0.97  
% 2.68/0.97  --instantiation_flag                    true
% 2.68/0.97  --inst_sos_flag                         false
% 2.68/0.97  --inst_sos_phase                        true
% 2.68/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/0.97  --inst_lit_sel_side                     num_symb
% 2.68/0.97  --inst_solver_per_active                1400
% 2.68/0.97  --inst_solver_calls_frac                1.
% 2.68/0.97  --inst_passive_queue_type               priority_queues
% 2.68/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/0.97  --inst_passive_queues_freq              [25;2]
% 2.68/0.97  --inst_dismatching                      true
% 2.68/0.97  --inst_eager_unprocessed_to_passive     true
% 2.68/0.97  --inst_prop_sim_given                   true
% 2.68/0.97  --inst_prop_sim_new                     false
% 2.68/0.97  --inst_subs_new                         false
% 2.68/0.97  --inst_eq_res_simp                      false
% 2.68/0.97  --inst_subs_given                       false
% 2.68/0.97  --inst_orphan_elimination               true
% 2.68/0.97  --inst_learning_loop_flag               true
% 2.68/0.97  --inst_learning_start                   3000
% 2.68/0.97  --inst_learning_factor                  2
% 2.68/0.97  --inst_start_prop_sim_after_learn       3
% 2.68/0.97  --inst_sel_renew                        solver
% 2.68/0.97  --inst_lit_activity_flag                true
% 2.68/0.97  --inst_restr_to_given                   false
% 2.68/0.97  --inst_activity_threshold               500
% 2.68/0.97  --inst_out_proof                        true
% 2.68/0.97  
% 2.68/0.97  ------ Resolution Options
% 2.68/0.97  
% 2.68/0.97  --resolution_flag                       true
% 2.68/0.97  --res_lit_sel                           adaptive
% 2.68/0.97  --res_lit_sel_side                      none
% 2.68/0.97  --res_ordering                          kbo
% 2.68/0.97  --res_to_prop_solver                    active
% 2.68/0.97  --res_prop_simpl_new                    false
% 2.68/0.97  --res_prop_simpl_given                  true
% 2.68/0.97  --res_passive_queue_type                priority_queues
% 2.68/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/0.97  --res_passive_queues_freq               [15;5]
% 2.68/0.97  --res_forward_subs                      full
% 2.68/0.97  --res_backward_subs                     full
% 2.68/0.97  --res_forward_subs_resolution           true
% 2.68/0.97  --res_backward_subs_resolution          true
% 2.68/0.97  --res_orphan_elimination                true
% 2.68/0.97  --res_time_limit                        2.
% 2.68/0.97  --res_out_proof                         true
% 2.68/0.97  
% 2.68/0.97  ------ Superposition Options
% 2.68/0.97  
% 2.68/0.97  --superposition_flag                    true
% 2.68/0.97  --sup_passive_queue_type                priority_queues
% 2.68/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.68/0.97  --demod_completeness_check              fast
% 2.68/0.97  --demod_use_ground                      true
% 2.68/0.97  --sup_to_prop_solver                    passive
% 2.68/0.97  --sup_prop_simpl_new                    true
% 2.68/0.97  --sup_prop_simpl_given                  true
% 2.68/0.97  --sup_fun_splitting                     false
% 2.68/0.97  --sup_smt_interval                      50000
% 2.68/0.97  
% 2.68/0.97  ------ Superposition Simplification Setup
% 2.68/0.97  
% 2.68/0.97  --sup_indices_passive                   []
% 2.68/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.97  --sup_full_bw                           [BwDemod]
% 2.68/0.97  --sup_immed_triv                        [TrivRules]
% 2.68/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.97  --sup_immed_bw_main                     []
% 2.68/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.97  
% 2.68/0.97  ------ Combination Options
% 2.68/0.97  
% 2.68/0.97  --comb_res_mult                         3
% 2.68/0.97  --comb_sup_mult                         2
% 2.68/0.97  --comb_inst_mult                        10
% 2.68/0.97  
% 2.68/0.97  ------ Debug Options
% 2.68/0.97  
% 2.68/0.97  --dbg_backtrace                         false
% 2.68/0.97  --dbg_dump_prop_clauses                 false
% 2.68/0.97  --dbg_dump_prop_clauses_file            -
% 2.68/0.97  --dbg_out_stat                          false
% 2.68/0.97  ------ Parsing...
% 2.68/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.68/0.97  
% 2.68/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.68/0.97  
% 2.68/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.68/0.97  
% 2.68/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.68/0.97  ------ Proving...
% 2.68/0.97  ------ Problem Properties 
% 2.68/0.97  
% 2.68/0.97  
% 2.68/0.97  clauses                                 22
% 2.68/0.97  conjectures                             3
% 2.68/0.97  EPR                                     7
% 2.68/0.97  Horn                                    14
% 2.68/0.97  unary                                   7
% 2.68/0.97  binary                                  7
% 2.68/0.97  lits                                    46
% 2.68/0.97  lits eq                                 7
% 2.68/0.97  fd_pure                                 0
% 2.68/0.97  fd_pseudo                               0
% 2.68/0.97  fd_cond                                 1
% 2.68/0.97  fd_pseudo_cond                          5
% 2.68/0.97  AC symbols                              0
% 2.68/0.97  
% 2.68/0.97  ------ Schedule dynamic 5 is on 
% 2.68/0.97  
% 2.68/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.68/0.97  
% 2.68/0.97  
% 2.68/0.97  ------ 
% 2.68/0.97  Current options:
% 2.68/0.97  ------ 
% 2.68/0.97  
% 2.68/0.97  ------ Input Options
% 2.68/0.97  
% 2.68/0.97  --out_options                           all
% 2.68/0.97  --tptp_safe_out                         true
% 2.68/0.97  --problem_path                          ""
% 2.68/0.97  --include_path                          ""
% 2.68/0.97  --clausifier                            res/vclausify_rel
% 2.68/0.97  --clausifier_options                    --mode clausify
% 2.68/0.97  --stdin                                 false
% 2.68/0.97  --stats_out                             all
% 2.68/0.97  
% 2.68/0.97  ------ General Options
% 2.68/0.97  
% 2.68/0.97  --fof                                   false
% 2.68/0.97  --time_out_real                         305.
% 2.68/0.97  --time_out_virtual                      -1.
% 2.68/0.97  --symbol_type_check                     false
% 2.68/0.97  --clausify_out                          false
% 2.68/0.97  --sig_cnt_out                           false
% 2.68/0.97  --trig_cnt_out                          false
% 2.68/0.97  --trig_cnt_out_tolerance                1.
% 2.68/0.97  --trig_cnt_out_sk_spl                   false
% 2.68/0.97  --abstr_cl_out                          false
% 2.68/0.97  
% 2.68/0.97  ------ Global Options
% 2.68/0.97  
% 2.68/0.97  --schedule                              default
% 2.68/0.97  --add_important_lit                     false
% 2.68/0.97  --prop_solver_per_cl                    1000
% 2.68/0.97  --min_unsat_core                        false
% 2.68/0.97  --soft_assumptions                      false
% 2.68/0.97  --soft_lemma_size                       3
% 2.68/0.97  --prop_impl_unit_size                   0
% 2.68/0.97  --prop_impl_unit                        []
% 2.68/0.97  --share_sel_clauses                     true
% 2.68/0.97  --reset_solvers                         false
% 2.68/0.97  --bc_imp_inh                            [conj_cone]
% 2.68/0.97  --conj_cone_tolerance                   3.
% 2.68/0.97  --extra_neg_conj                        none
% 2.68/0.97  --large_theory_mode                     true
% 2.68/0.97  --prolific_symb_bound                   200
% 2.68/0.97  --lt_threshold                          2000
% 2.68/0.97  --clause_weak_htbl                      true
% 2.68/0.97  --gc_record_bc_elim                     false
% 2.68/0.97  
% 2.68/0.97  ------ Preprocessing Options
% 2.68/0.97  
% 2.68/0.97  --preprocessing_flag                    true
% 2.68/0.97  --time_out_prep_mult                    0.1
% 2.68/0.97  --splitting_mode                        input
% 2.68/0.97  --splitting_grd                         true
% 2.68/0.97  --splitting_cvd                         false
% 2.68/0.97  --splitting_cvd_svl                     false
% 2.68/0.97  --splitting_nvd                         32
% 2.68/0.97  --sub_typing                            true
% 2.68/0.97  --prep_gs_sim                           true
% 2.68/0.97  --prep_unflatten                        true
% 2.68/0.97  --prep_res_sim                          true
% 2.68/0.97  --prep_upred                            true
% 2.68/0.97  --prep_sem_filter                       exhaustive
% 2.68/0.97  --prep_sem_filter_out                   false
% 2.68/0.97  --pred_elim                             true
% 2.68/0.97  --res_sim_input                         true
% 2.68/0.97  --eq_ax_congr_red                       true
% 2.68/0.97  --pure_diseq_elim                       true
% 2.68/0.97  --brand_transform                       false
% 2.68/0.97  --non_eq_to_eq                          false
% 2.68/0.97  --prep_def_merge                        true
% 2.68/0.97  --prep_def_merge_prop_impl              false
% 2.68/0.97  --prep_def_merge_mbd                    true
% 2.68/0.97  --prep_def_merge_tr_red                 false
% 2.68/0.97  --prep_def_merge_tr_cl                  false
% 2.68/0.97  --smt_preprocessing                     true
% 2.68/0.97  --smt_ac_axioms                         fast
% 2.68/0.97  --preprocessed_out                      false
% 2.68/0.97  --preprocessed_stats                    false
% 2.68/0.97  
% 2.68/0.97  ------ Abstraction refinement Options
% 2.68/0.97  
% 2.68/0.97  --abstr_ref                             []
% 2.68/0.97  --abstr_ref_prep                        false
% 2.68/0.97  --abstr_ref_until_sat                   false
% 2.68/0.97  --abstr_ref_sig_restrict                funpre
% 2.68/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/0.97  --abstr_ref_under                       []
% 2.68/0.97  
% 2.68/0.97  ------ SAT Options
% 2.68/0.97  
% 2.68/0.97  --sat_mode                              false
% 2.68/0.97  --sat_fm_restart_options                ""
% 2.68/0.97  --sat_gr_def                            false
% 2.68/0.97  --sat_epr_types                         true
% 2.68/0.97  --sat_non_cyclic_types                  false
% 2.68/0.97  --sat_finite_models                     false
% 2.68/0.97  --sat_fm_lemmas                         false
% 2.68/0.97  --sat_fm_prep                           false
% 2.68/0.97  --sat_fm_uc_incr                        true
% 2.68/0.97  --sat_out_model                         small
% 2.68/0.97  --sat_out_clauses                       false
% 2.68/0.97  
% 2.68/0.97  ------ QBF Options
% 2.68/0.97  
% 2.68/0.97  --qbf_mode                              false
% 2.68/0.97  --qbf_elim_univ                         false
% 2.68/0.97  --qbf_dom_inst                          none
% 2.68/0.97  --qbf_dom_pre_inst                      false
% 2.68/0.97  --qbf_sk_in                             false
% 2.68/0.97  --qbf_pred_elim                         true
% 2.68/0.97  --qbf_split                             512
% 2.68/0.97  
% 2.68/0.97  ------ BMC1 Options
% 2.68/0.97  
% 2.68/0.97  --bmc1_incremental                      false
% 2.68/0.97  --bmc1_axioms                           reachable_all
% 2.68/0.97  --bmc1_min_bound                        0
% 2.68/0.97  --bmc1_max_bound                        -1
% 2.68/0.97  --bmc1_max_bound_default                -1
% 2.68/0.97  --bmc1_symbol_reachability              true
% 2.68/0.97  --bmc1_property_lemmas                  false
% 2.68/0.97  --bmc1_k_induction                      false
% 2.68/0.97  --bmc1_non_equiv_states                 false
% 2.68/0.97  --bmc1_deadlock                         false
% 2.68/0.97  --bmc1_ucm                              false
% 2.68/0.97  --bmc1_add_unsat_core                   none
% 2.68/0.97  --bmc1_unsat_core_children              false
% 2.68/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/0.97  --bmc1_out_stat                         full
% 2.68/0.97  --bmc1_ground_init                      false
% 2.68/0.97  --bmc1_pre_inst_next_state              false
% 2.68/0.97  --bmc1_pre_inst_state                   false
% 2.68/0.97  --bmc1_pre_inst_reach_state             false
% 2.68/0.97  --bmc1_out_unsat_core                   false
% 2.68/0.97  --bmc1_aig_witness_out                  false
% 2.68/0.97  --bmc1_verbose                          false
% 2.68/0.97  --bmc1_dump_clauses_tptp                false
% 2.68/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.68/0.97  --bmc1_dump_file                        -
% 2.68/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.68/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.68/0.97  --bmc1_ucm_extend_mode                  1
% 2.68/0.97  --bmc1_ucm_init_mode                    2
% 2.68/0.97  --bmc1_ucm_cone_mode                    none
% 2.68/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.68/0.97  --bmc1_ucm_relax_model                  4
% 2.68/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.68/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/0.97  --bmc1_ucm_layered_model                none
% 2.68/0.97  --bmc1_ucm_max_lemma_size               10
% 2.68/0.97  
% 2.68/0.97  ------ AIG Options
% 2.68/0.97  
% 2.68/0.97  --aig_mode                              false
% 2.68/0.97  
% 2.68/0.97  ------ Instantiation Options
% 2.68/0.97  
% 2.68/0.97  --instantiation_flag                    true
% 2.68/0.97  --inst_sos_flag                         false
% 2.68/0.97  --inst_sos_phase                        true
% 2.68/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/0.97  --inst_lit_sel_side                     none
% 2.68/0.97  --inst_solver_per_active                1400
% 2.68/0.97  --inst_solver_calls_frac                1.
% 2.68/0.97  --inst_passive_queue_type               priority_queues
% 2.68/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/0.97  --inst_passive_queues_freq              [25;2]
% 2.68/0.97  --inst_dismatching                      true
% 2.68/0.97  --inst_eager_unprocessed_to_passive     true
% 2.68/0.97  --inst_prop_sim_given                   true
% 2.68/0.97  --inst_prop_sim_new                     false
% 2.68/0.97  --inst_subs_new                         false
% 2.68/0.97  --inst_eq_res_simp                      false
% 2.68/0.97  --inst_subs_given                       false
% 2.68/0.97  --inst_orphan_elimination               true
% 2.68/0.97  --inst_learning_loop_flag               true
% 2.68/0.97  --inst_learning_start                   3000
% 2.68/0.97  --inst_learning_factor                  2
% 2.68/0.97  --inst_start_prop_sim_after_learn       3
% 2.68/0.97  --inst_sel_renew                        solver
% 2.68/0.97  --inst_lit_activity_flag                true
% 2.68/0.97  --inst_restr_to_given                   false
% 2.68/0.97  --inst_activity_threshold               500
% 2.68/0.97  --inst_out_proof                        true
% 2.68/0.97  
% 2.68/0.97  ------ Resolution Options
% 2.68/0.97  
% 2.68/0.97  --resolution_flag                       false
% 2.68/0.97  --res_lit_sel                           adaptive
% 2.68/0.97  --res_lit_sel_side                      none
% 2.68/0.97  --res_ordering                          kbo
% 2.68/0.97  --res_to_prop_solver                    active
% 2.68/0.97  --res_prop_simpl_new                    false
% 2.68/0.97  --res_prop_simpl_given                  true
% 2.68/0.97  --res_passive_queue_type                priority_queues
% 2.68/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/0.97  --res_passive_queues_freq               [15;5]
% 2.68/0.97  --res_forward_subs                      full
% 2.68/0.97  --res_backward_subs                     full
% 2.68/0.97  --res_forward_subs_resolution           true
% 2.68/0.97  --res_backward_subs_resolution          true
% 2.68/0.97  --res_orphan_elimination                true
% 2.68/0.97  --res_time_limit                        2.
% 2.68/0.97  --res_out_proof                         true
% 2.68/0.97  
% 2.68/0.97  ------ Superposition Options
% 2.68/0.97  
% 2.68/0.97  --superposition_flag                    true
% 2.68/0.97  --sup_passive_queue_type                priority_queues
% 2.68/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.68/0.97  --demod_completeness_check              fast
% 2.68/0.97  --demod_use_ground                      true
% 2.68/0.97  --sup_to_prop_solver                    passive
% 2.68/0.97  --sup_prop_simpl_new                    true
% 2.68/0.97  --sup_prop_simpl_given                  true
% 2.68/0.97  --sup_fun_splitting                     false
% 2.68/0.97  --sup_smt_interval                      50000
% 2.68/0.97  
% 2.68/0.97  ------ Superposition Simplification Setup
% 2.68/0.97  
% 2.68/0.97  --sup_indices_passive                   []
% 2.68/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.97  --sup_full_bw                           [BwDemod]
% 2.68/0.97  --sup_immed_triv                        [TrivRules]
% 2.68/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.97  --sup_immed_bw_main                     []
% 2.68/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/0.97  
% 2.68/0.97  ------ Combination Options
% 2.68/0.97  
% 2.68/0.97  --comb_res_mult                         3
% 2.68/0.97  --comb_sup_mult                         2
% 2.68/0.97  --comb_inst_mult                        10
% 2.68/0.97  
% 2.68/0.97  ------ Debug Options
% 2.68/0.97  
% 2.68/0.97  --dbg_backtrace                         false
% 2.68/0.97  --dbg_dump_prop_clauses                 false
% 2.68/0.97  --dbg_dump_prop_clauses_file            -
% 2.68/0.97  --dbg_out_stat                          false
% 2.68/0.97  
% 2.68/0.97  
% 2.68/0.97  
% 2.68/0.97  
% 2.68/0.97  ------ Proving...
% 2.68/0.97  
% 2.68/0.97  
% 2.68/0.97  % SZS status Theorem for theBenchmark.p
% 2.68/0.97  
% 2.68/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.68/0.97  
% 2.68/0.97  fof(f2,axiom,(
% 2.68/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f22,plain,(
% 2.68/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.68/0.97    inference(ennf_transformation,[],[f2])).
% 2.68/0.97  
% 2.68/0.97  fof(f33,plain,(
% 2.68/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.68/0.97    inference(nnf_transformation,[],[f22])).
% 2.68/0.97  
% 2.68/0.97  fof(f34,plain,(
% 2.68/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.68/0.97    inference(rectify,[],[f33])).
% 2.68/0.97  
% 2.68/0.97  fof(f35,plain,(
% 2.68/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.68/0.97    introduced(choice_axiom,[])).
% 2.68/0.97  
% 2.68/0.97  fof(f36,plain,(
% 2.68/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.68/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 2.68/0.97  
% 2.68/0.97  fof(f51,plain,(
% 2.68/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f36])).
% 2.68/0.97  
% 2.68/0.97  fof(f8,axiom,(
% 2.68/0.97    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f64,plain,(
% 2.68/0.97    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f8])).
% 2.68/0.97  
% 2.68/0.97  fof(f16,axiom,(
% 2.68/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f72,plain,(
% 2.68/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.68/0.97    inference(cnf_transformation,[],[f16])).
% 2.68/0.97  
% 2.68/0.97  fof(f10,axiom,(
% 2.68/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f66,plain,(
% 2.68/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f10])).
% 2.68/0.97  
% 2.68/0.97  fof(f11,axiom,(
% 2.68/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f67,plain,(
% 2.68/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f11])).
% 2.68/0.97  
% 2.68/0.97  fof(f12,axiom,(
% 2.68/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f68,plain,(
% 2.68/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f12])).
% 2.68/0.97  
% 2.68/0.97  fof(f13,axiom,(
% 2.68/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f69,plain,(
% 2.68/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f13])).
% 2.68/0.97  
% 2.68/0.97  fof(f14,axiom,(
% 2.68/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f70,plain,(
% 2.68/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f14])).
% 2.68/0.97  
% 2.68/0.97  fof(f15,axiom,(
% 2.68/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f71,plain,(
% 2.68/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f15])).
% 2.68/0.97  
% 2.68/0.97  fof(f79,plain,(
% 2.68/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.68/0.97    inference(definition_unfolding,[],[f70,f71])).
% 2.68/0.97  
% 2.68/0.97  fof(f80,plain,(
% 2.68/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.68/0.97    inference(definition_unfolding,[],[f69,f79])).
% 2.68/0.97  
% 2.68/0.97  fof(f81,plain,(
% 2.68/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.68/0.97    inference(definition_unfolding,[],[f68,f80])).
% 2.68/0.97  
% 2.68/0.97  fof(f82,plain,(
% 2.68/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.68/0.97    inference(definition_unfolding,[],[f67,f81])).
% 2.68/0.97  
% 2.68/0.97  fof(f83,plain,(
% 2.68/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.68/0.97    inference(definition_unfolding,[],[f66,f82])).
% 2.68/0.97  
% 2.68/0.97  fof(f84,plain,(
% 2.68/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.68/0.97    inference(definition_unfolding,[],[f72,f83])).
% 2.68/0.97  
% 2.68/0.97  fof(f93,plain,(
% 2.68/0.97    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 2.68/0.97    inference(definition_unfolding,[],[f64,f84])).
% 2.68/0.97  
% 2.68/0.97  fof(f18,axiom,(
% 2.68/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f25,plain,(
% 2.68/0.97    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.68/0.97    inference(ennf_transformation,[],[f18])).
% 2.68/0.97  
% 2.68/0.97  fof(f26,plain,(
% 2.68/0.97    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.68/0.97    inference(flattening,[],[f25])).
% 2.68/0.97  
% 2.68/0.97  fof(f74,plain,(
% 2.68/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.68/0.97    inference(cnf_transformation,[],[f26])).
% 2.68/0.97  
% 2.68/0.97  fof(f19,conjecture,(
% 2.68/0.97    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.68/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.97  
% 2.68/0.97  fof(f20,negated_conjecture,(
% 2.68/0.97    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.68/0.97    inference(negated_conjecture,[],[f19])).
% 2.68/0.97  
% 2.68/0.97  fof(f27,plain,(
% 2.68/0.97    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 2.68/0.97    inference(ennf_transformation,[],[f20])).
% 2.68/0.97  
% 2.68/0.97  fof(f28,plain,(
% 2.68/0.97    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 2.68/0.97    inference(flattening,[],[f27])).
% 2.68/0.97  
% 2.68/0.97  fof(f46,plain,(
% 2.68/0.97    ( ! [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) => (~r1_tarski(X0,sK5) & ~v1_xboole_0(k3_xboole_0(X0,sK5)))) )),
% 2.68/0.97    introduced(choice_axiom,[])).
% 2.68/0.97  
% 2.68/0.97  fof(f45,plain,(
% 2.68/0.97    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK4,X1) & ~v1_xboole_0(k3_xboole_0(sK4,X1))) & v1_zfmisc_1(sK4) & ~v1_xboole_0(sK4))),
% 2.68/0.97    introduced(choice_axiom,[])).
% 2.68/0.97  
% 2.68/0.97  fof(f47,plain,(
% 2.68/0.97    (~r1_tarski(sK4,sK5) & ~v1_xboole_0(k3_xboole_0(sK4,sK5))) & v1_zfmisc_1(sK4) & ~v1_xboole_0(sK4)),
% 2.68/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f46,f45])).
% 2.68/0.97  
% 2.68/0.97  fof(f76,plain,(
% 2.68/0.97    v1_zfmisc_1(sK4)),
% 2.68/0.97    inference(cnf_transformation,[],[f47])).
% 2.68/0.97  
% 2.68/0.97  fof(f75,plain,(
% 2.68/0.97    ~v1_xboole_0(sK4)),
% 2.68/0.97    inference(cnf_transformation,[],[f47])).
% 2.68/0.97  
% 2.68/0.97  fof(f77,plain,(
% 2.68/0.97    ~v1_xboole_0(k3_xboole_0(sK4,sK5))),
% 2.68/0.97    inference(cnf_transformation,[],[f47])).
% 2.68/0.98  
% 2.68/0.98  fof(f95,plain,(
% 2.68/0.98    ~v1_xboole_0(k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))),
% 2.68/0.98    inference(definition_unfolding,[],[f77,f84])).
% 2.68/0.98  
% 2.68/0.98  fof(f3,axiom,(
% 2.68/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f37,plain,(
% 2.68/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.68/0.98    inference(nnf_transformation,[],[f3])).
% 2.68/0.98  
% 2.68/0.98  fof(f38,plain,(
% 2.68/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.68/0.98    inference(flattening,[],[f37])).
% 2.68/0.98  
% 2.68/0.98  fof(f39,plain,(
% 2.68/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.68/0.98    inference(rectify,[],[f38])).
% 2.68/0.98  
% 2.68/0.98  fof(f40,plain,(
% 2.68/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.68/0.98    introduced(choice_axiom,[])).
% 2.68/0.98  
% 2.68/0.98  fof(f41,plain,(
% 2.68/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.68/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 2.68/0.98  
% 2.68/0.98  fof(f55,plain,(
% 2.68/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.68/0.98    inference(cnf_transformation,[],[f41])).
% 2.68/0.98  
% 2.68/0.98  fof(f7,axiom,(
% 2.68/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f63,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.68/0.98    inference(cnf_transformation,[],[f7])).
% 2.68/0.98  
% 2.68/0.98  fof(f85,plain,(
% 2.68/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.68/0.98    inference(definition_unfolding,[],[f63,f84])).
% 2.68/0.98  
% 2.68/0.98  fof(f89,plain,(
% 2.68/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 2.68/0.98    inference(definition_unfolding,[],[f55,f85])).
% 2.68/0.98  
% 2.68/0.98  fof(f96,plain,(
% 2.68/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.68/0.98    inference(equality_resolution,[],[f89])).
% 2.68/0.98  
% 2.68/0.98  fof(f5,axiom,(
% 2.68/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.68/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/0.98  
% 2.68/0.98  fof(f21,plain,(
% 2.68/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.68/0.98    inference(rectify,[],[f5])).
% 2.68/0.98  
% 2.68/0.98  fof(f60,plain,(
% 2.68/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.68/0.98    inference(cnf_transformation,[],[f21])).
% 2.68/0.98  
% 2.68/0.98  fof(f92,plain,(
% 2.68/0.98    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.68/0.98    inference(definition_unfolding,[],[f60,f84])).
% 2.68/0.98  
% 2.68/0.98  fof(f54,plain,(
% 2.68/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.68/0.98    inference(cnf_transformation,[],[f41])).
% 2.68/0.98  
% 2.68/0.98  fof(f90,plain,(
% 2.68/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 2.68/0.98    inference(definition_unfolding,[],[f54,f85])).
% 2.68/0.98  
% 2.68/0.98  fof(f97,plain,(
% 2.68/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.68/0.98    inference(equality_resolution,[],[f90])).
% 2.68/0.98  
% 2.68/0.98  fof(f53,plain,(
% 2.68/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.68/0.98    inference(cnf_transformation,[],[f41])).
% 2.68/0.98  
% 2.68/0.98  fof(f91,plain,(
% 2.68/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 2.68/0.98    inference(definition_unfolding,[],[f53,f85])).
% 2.68/0.98  
% 2.68/0.98  fof(f98,plain,(
% 2.68/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.68/0.98    inference(equality_resolution,[],[f91])).
% 2.68/0.98  
% 2.68/0.98  fof(f52,plain,(
% 2.68/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 2.68/0.98    inference(cnf_transformation,[],[f36])).
% 2.68/0.98  
% 2.68/0.98  fof(f78,plain,(
% 2.68/0.98    ~r1_tarski(sK4,sK5)),
% 2.68/0.98    inference(cnf_transformation,[],[f47])).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3,plain,
% 2.68/0.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.68/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1289,plain,
% 2.68/0.98      ( r1_tarski(X0,X1) = iProver_top
% 2.68/0.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_15,plain,
% 2.68/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 2.68/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1278,plain,
% 2.68/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_18,plain,
% 2.68/0.98      ( ~ r1_tarski(X0,X1)
% 2.68/0.98      | ~ v1_zfmisc_1(X1)
% 2.68/0.98      | v1_xboole_0(X0)
% 2.68/0.98      | v1_xboole_0(X1)
% 2.68/0.98      | X1 = X0 ),
% 2.68/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_21,negated_conjecture,
% 2.68/0.98      ( v1_zfmisc_1(sK4) ),
% 2.68/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_241,plain,
% 2.68/0.98      ( ~ r1_tarski(X0,X1)
% 2.68/0.98      | v1_xboole_0(X0)
% 2.68/0.98      | v1_xboole_0(X1)
% 2.68/0.98      | X1 = X0
% 2.68/0.98      | sK4 != X1 ),
% 2.68/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_242,plain,
% 2.68/0.98      ( ~ r1_tarski(X0,sK4)
% 2.68/0.98      | v1_xboole_0(X0)
% 2.68/0.98      | v1_xboole_0(sK4)
% 2.68/0.98      | sK4 = X0 ),
% 2.68/0.98      inference(unflattening,[status(thm)],[c_241]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_22,negated_conjecture,
% 2.68/0.98      ( ~ v1_xboole_0(sK4) ),
% 2.68/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_246,plain,
% 2.68/0.98      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK4) | sK4 = X0 ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_242,c_22]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_247,plain,
% 2.68/0.98      ( ~ r1_tarski(X0,sK4) | v1_xboole_0(X0) | sK4 = X0 ),
% 2.68/0.98      inference(renaming,[status(thm)],[c_246]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1272,plain,
% 2.68/0.98      ( sK4 = X0
% 2.68/0.98      | r1_tarski(X0,sK4) != iProver_top
% 2.68/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2133,plain,
% 2.68/0.98      ( k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) = sK4
% 2.68/0.98      | v1_xboole_0(k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))) = iProver_top ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_1278,c_1272]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_20,negated_conjecture,
% 2.68/0.98      ( ~ v1_xboole_0(k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))) ),
% 2.68/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1274,plain,
% 2.68/0.98      ( v1_xboole_0(k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2364,plain,
% 2.68/0.98      ( k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_2133,c_1274]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_8,plain,
% 2.68/0.98      ( ~ r2_hidden(X0,X1)
% 2.68/0.98      | r2_hidden(X0,X2)
% 2.68/0.98      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 2.68/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1284,plain,
% 2.68/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.68/0.98      | r2_hidden(X0,X2) = iProver_top
% 2.68/0.98      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3856,plain,
% 2.68/0.98      ( r2_hidden(X0,k5_xboole_0(sK4,sK4)) = iProver_top
% 2.68/0.98      | r2_hidden(X0,sK5) = iProver_top
% 2.68/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_2364,c_1284]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_12,plain,
% 2.68/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 2.68/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_9,plain,
% 2.68/0.98      ( ~ r2_hidden(X0,X1)
% 2.68/0.98      | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
% 2.68/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1283,plain,
% 2.68/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.68/0.98      | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_3813,plain,
% 2.68/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.68/0.98      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_12,c_1283]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_10,plain,
% 2.68/0.98      ( r2_hidden(X0,X1)
% 2.68/0.98      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 2.68/0.98      inference(cnf_transformation,[],[f98]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1282,plain,
% 2.68/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.68/0.98      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2916,plain,
% 2.68/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.68/0.98      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_12,c_1282]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_4072,plain,
% 2.68/0.98      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 2.68/0.98      inference(global_propositional_subsumption,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_3813,c_2916]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_4895,plain,
% 2.68/0.98      ( r2_hidden(X0,sK5) = iProver_top
% 2.68/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 2.68/0.98      inference(forward_subsumption_resolution,
% 2.68/0.98                [status(thm)],
% 2.68/0.98                [c_3856,c_4072]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_4898,plain,
% 2.68/0.98      ( r1_tarski(sK4,X0) = iProver_top
% 2.68/0.98      | r2_hidden(sK1(sK4,X0),sK5) = iProver_top ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_1289,c_4895]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_2,plain,
% 2.68/0.98      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 2.68/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_1290,plain,
% 2.68/0.98      ( r1_tarski(X0,X1) = iProver_top
% 2.68/0.98      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_5087,plain,
% 2.68/0.98      ( r1_tarski(sK4,sK5) = iProver_top ),
% 2.68/0.98      inference(superposition,[status(thm)],[c_4898,c_1290]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_19,negated_conjecture,
% 2.68/0.98      ( ~ r1_tarski(sK4,sK5) ),
% 2.68/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(c_26,plain,
% 2.68/0.98      ( r1_tarski(sK4,sK5) != iProver_top ),
% 2.68/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.68/0.98  
% 2.68/0.98  cnf(contradiction,plain,
% 2.68/0.98      ( $false ),
% 2.68/0.98      inference(minisat,[status(thm)],[c_5087,c_26]) ).
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.68/0.98  
% 2.68/0.98  ------                               Statistics
% 2.68/0.98  
% 2.68/0.98  ------ General
% 2.68/0.98  
% 2.68/0.98  abstr_ref_over_cycles:                  0
% 2.68/0.98  abstr_ref_under_cycles:                 0
% 2.68/0.98  gc_basic_clause_elim:                   0
% 2.68/0.98  forced_gc_time:                         0
% 2.68/0.98  parsing_time:                           0.01
% 2.68/0.98  unif_index_cands_time:                  0.
% 2.68/0.98  unif_index_add_time:                    0.
% 2.68/0.98  orderings_time:                         0.
% 2.68/0.98  out_proof_time:                         0.008
% 2.68/0.98  total_time:                             0.17
% 2.68/0.98  num_of_symbols:                         45
% 2.68/0.98  num_of_terms:                           5007
% 2.68/0.98  
% 2.68/0.98  ------ Preprocessing
% 2.68/0.98  
% 2.68/0.98  num_of_splits:                          0
% 2.68/0.98  num_of_split_atoms:                     0
% 2.68/0.98  num_of_reused_defs:                     0
% 2.68/0.98  num_eq_ax_congr_red:                    27
% 2.68/0.98  num_of_sem_filtered_clauses:            1
% 2.68/0.98  num_of_subtypes:                        0
% 2.68/0.98  monotx_restored_types:                  0
% 2.68/0.98  sat_num_of_epr_types:                   0
% 2.68/0.98  sat_num_of_non_cyclic_types:            0
% 2.68/0.98  sat_guarded_non_collapsed_types:        0
% 2.68/0.98  num_pure_diseq_elim:                    0
% 2.68/0.98  simp_replaced_by:                       0
% 2.68/0.98  res_preprocessed:                       106
% 2.68/0.98  prep_upred:                             0
% 2.68/0.98  prep_unflattend:                        59
% 2.68/0.98  smt_new_axioms:                         0
% 2.68/0.98  pred_elim_cands:                        3
% 2.68/0.98  pred_elim:                              1
% 2.68/0.98  pred_elim_cl:                           1
% 2.68/0.98  pred_elim_cycles:                       5
% 2.68/0.98  merged_defs:                            0
% 2.68/0.98  merged_defs_ncl:                        0
% 2.68/0.98  bin_hyper_res:                          0
% 2.68/0.98  prep_cycles:                            4
% 2.68/0.98  pred_elim_time:                         0.007
% 2.68/0.98  splitting_time:                         0.
% 2.68/0.98  sem_filter_time:                        0.
% 2.68/0.98  monotx_time:                            0.001
% 2.68/0.98  subtype_inf_time:                       0.
% 2.68/0.98  
% 2.68/0.98  ------ Problem properties
% 2.68/0.98  
% 2.68/0.98  clauses:                                22
% 2.68/0.98  conjectures:                            3
% 2.68/0.98  epr:                                    7
% 2.68/0.98  horn:                                   14
% 2.68/0.98  ground:                                 4
% 2.68/0.98  unary:                                  7
% 2.68/0.98  binary:                                 7
% 2.68/0.98  lits:                                   46
% 2.68/0.98  lits_eq:                                7
% 2.68/0.98  fd_pure:                                0
% 2.68/0.98  fd_pseudo:                              0
% 2.68/0.98  fd_cond:                                1
% 2.68/0.98  fd_pseudo_cond:                         5
% 2.68/0.98  ac_symbols:                             0
% 2.68/0.98  
% 2.68/0.98  ------ Propositional Solver
% 2.68/0.98  
% 2.68/0.98  prop_solver_calls:                      27
% 2.68/0.98  prop_fast_solver_calls:                 656
% 2.68/0.98  smt_solver_calls:                       0
% 2.68/0.98  smt_fast_solver_calls:                  0
% 2.68/0.98  prop_num_of_clauses:                    1906
% 2.68/0.98  prop_preprocess_simplified:             7278
% 2.68/0.98  prop_fo_subsumed:                       4
% 2.68/0.98  prop_solver_time:                       0.
% 2.68/0.98  smt_solver_time:                        0.
% 2.68/0.98  smt_fast_solver_time:                   0.
% 2.68/0.98  prop_fast_solver_time:                  0.
% 2.68/0.98  prop_unsat_core_time:                   0.
% 2.68/0.98  
% 2.68/0.98  ------ QBF
% 2.68/0.98  
% 2.68/0.98  qbf_q_res:                              0
% 2.68/0.98  qbf_num_tautologies:                    0
% 2.68/0.98  qbf_prep_cycles:                        0
% 2.68/0.98  
% 2.68/0.98  ------ BMC1
% 2.68/0.98  
% 2.68/0.98  bmc1_current_bound:                     -1
% 2.68/0.98  bmc1_last_solved_bound:                 -1
% 2.68/0.98  bmc1_unsat_core_size:                   -1
% 2.68/0.98  bmc1_unsat_core_parents_size:           -1
% 2.68/0.98  bmc1_merge_next_fun:                    0
% 2.68/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.68/0.98  
% 2.68/0.98  ------ Instantiation
% 2.68/0.98  
% 2.68/0.98  inst_num_of_clauses:                    574
% 2.68/0.98  inst_num_in_passive:                    352
% 2.68/0.98  inst_num_in_active:                     195
% 2.68/0.98  inst_num_in_unprocessed:                27
% 2.68/0.98  inst_num_of_loops:                      210
% 2.68/0.98  inst_num_of_learning_restarts:          0
% 2.68/0.98  inst_num_moves_active_passive:          14
% 2.68/0.98  inst_lit_activity:                      0
% 2.68/0.98  inst_lit_activity_moves:                0
% 2.68/0.98  inst_num_tautologies:                   0
% 2.68/0.98  inst_num_prop_implied:                  0
% 2.68/0.98  inst_num_existing_simplified:           0
% 2.68/0.98  inst_num_eq_res_simplified:             0
% 2.68/0.98  inst_num_child_elim:                    0
% 2.68/0.98  inst_num_of_dismatching_blockings:      115
% 2.68/0.98  inst_num_of_non_proper_insts:           395
% 2.68/0.98  inst_num_of_duplicates:                 0
% 2.68/0.98  inst_inst_num_from_inst_to_res:         0
% 2.68/0.98  inst_dismatching_checking_time:         0.
% 2.68/0.98  
% 2.68/0.98  ------ Resolution
% 2.68/0.98  
% 2.68/0.98  res_num_of_clauses:                     0
% 2.68/0.98  res_num_in_passive:                     0
% 2.68/0.98  res_num_in_active:                      0
% 2.68/0.98  res_num_of_loops:                       110
% 2.68/0.98  res_forward_subset_subsumed:            32
% 2.68/0.98  res_backward_subset_subsumed:           0
% 2.68/0.98  res_forward_subsumed:                   0
% 2.68/0.98  res_backward_subsumed:                  0
% 2.68/0.98  res_forward_subsumption_resolution:     1
% 2.68/0.98  res_backward_subsumption_resolution:    0
% 2.68/0.98  res_clause_to_clause_subsumption:       449
% 2.68/0.98  res_orphan_elimination:                 0
% 2.68/0.98  res_tautology_del:                      26
% 2.68/0.98  res_num_eq_res_simplified:              0
% 2.68/0.98  res_num_sel_changes:                    0
% 2.68/0.98  res_moves_from_active_to_pass:          0
% 2.68/0.98  
% 2.68/0.98  ------ Superposition
% 2.68/0.98  
% 2.68/0.98  sup_time_total:                         0.
% 2.68/0.98  sup_time_generating:                    0.
% 2.68/0.98  sup_time_sim_full:                      0.
% 2.68/0.98  sup_time_sim_immed:                     0.
% 2.68/0.98  
% 2.68/0.98  sup_num_of_clauses:                     90
% 2.68/0.98  sup_num_in_active:                      40
% 2.68/0.98  sup_num_in_passive:                     50
% 2.68/0.98  sup_num_of_loops:                       40
% 2.68/0.98  sup_fw_superposition:                   51
% 2.68/0.98  sup_bw_superposition:                   55
% 2.68/0.98  sup_immediate_simplified:               16
% 2.68/0.98  sup_given_eliminated:                   0
% 2.68/0.98  comparisons_done:                       0
% 2.68/0.98  comparisons_avoided:                    0
% 2.68/0.98  
% 2.68/0.98  ------ Simplifications
% 2.68/0.98  
% 2.68/0.98  
% 2.68/0.98  sim_fw_subset_subsumed:                 3
% 2.68/0.98  sim_bw_subset_subsumed:                 6
% 2.68/0.98  sim_fw_subsumed:                        6
% 2.68/0.98  sim_bw_subsumed:                        1
% 2.68/0.98  sim_fw_subsumption_res:                 1
% 2.68/0.98  sim_bw_subsumption_res:                 0
% 2.68/0.98  sim_tautology_del:                      11
% 2.68/0.98  sim_eq_tautology_del:                   4
% 2.68/0.98  sim_eq_res_simp:                        1
% 2.68/0.98  sim_fw_demodulated:                     2
% 2.68/0.98  sim_bw_demodulated:                     1
% 2.68/0.98  sim_light_normalised:                   2
% 2.68/0.98  sim_joinable_taut:                      0
% 2.68/0.98  sim_joinable_simp:                      0
% 2.68/0.98  sim_ac_normalised:                      0
% 2.68/0.98  sim_smt_subsumption:                    0
% 2.68/0.98  
%------------------------------------------------------------------------------

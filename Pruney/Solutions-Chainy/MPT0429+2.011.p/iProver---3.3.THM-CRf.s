%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:42 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 332 expanded)
%              Number of clauses        :   61 ( 119 expanded)
%              Number of leaves         :   24 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  307 ( 752 expanded)
%              Number of equality atoms :  127 ( 321 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0)))
      | ~ m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f10,axiom,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f77,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f78,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f53,f77])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ( k1_xboole_0 != X0
               => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              | k1_xboole_0 = X0
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
              | k1_xboole_0 = X0
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f30])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f73,f56])).

fof(f22,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f22])).

fof(f34,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f42])).

fof(f75,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    ~ m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(definition_unfolding,[],[f75,f77])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f66,f77])).

fof(f87,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f80])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK0(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_20,plain,
    ( v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4068,plain,
    ( v1_xboole_0(k1_subset_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4087,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4081,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4412,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4087,c_4081])).

cnf(c_4553,plain,
    ( k1_subset_1(X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_4068,c_4412])).

cnf(c_21,plain,
    ( ~ m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))
    | r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_19,plain,
    ( m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_151,plain,
    ( r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_19])).

cnf(c_4062,plain,
    ( r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_4578,plain,
    ( r1_tarski(o_0_0_xboole_0,k3_subset_1(X0,o_0_0_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4553,c_4062])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4078,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | m1_subset_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4065,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4725,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_4065])).

cnf(c_26,negated_conjecture,
    ( ~ m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4063,plain,
    ( m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5063,plain,
    ( k1_zfmisc_1(sK1) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4725,c_4063])).

cnf(c_23,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4066,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5088,plain,
    ( k1_zfmisc_1(sK1) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5063,c_4066])).

cnf(c_25,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4064,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5095,plain,
    ( m1_subset_1(X0,sK1) = iProver_top
    | m1_subset_1(X1,k1_xboole_0) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5088,c_4064])).

cnf(c_5232,plain,
    ( m1_subset_1(X0,sK1) = iProver_top
    | m1_subset_1(k1_zfmisc_1(X1),k1_xboole_0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4078,c_5095])).

cnf(c_5,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4082,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4084,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4340,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4082,c_4084])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4071,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4365,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4340,c_4071])).

cnf(c_4372,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4365])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4073,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4465,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4073,c_4084])).

cnf(c_4621,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4082,c_4465])).

cnf(c_4633,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4621,c_4340])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4076,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4645,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4633,c_4076])).

cnf(c_4668,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4645,c_4633])).

cnf(c_9,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4079,plain,
    ( k1_zfmisc_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_tarski(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4756,plain,
    ( k1_zfmisc_1(X0) = k1_xboole_0
    | r1_tarski(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4079,c_4365])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4085,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4389,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4340,c_4085])).

cnf(c_4854,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK0(k1_xboole_0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4756,c_4389])).

cnf(c_5096,plain,
    ( r2_hidden(X0,k1_xboole_0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5088,c_4078])).

cnf(c_5182,plain,
    ( r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5096,c_4365])).

cnf(c_5193,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4854,c_5182])).

cnf(c_5566,plain,
    ( r2_hidden(X0,k1_xboole_0) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5193,c_4078])).

cnf(c_5580,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5566])).

cnf(c_5655,plain,
    ( r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5232,c_4372,c_4668,c_5580])).

cnf(c_5663,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4578,c_5655])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:41:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.48/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.00  
% 3.48/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/1.00  
% 3.48/1.00  ------  iProver source info
% 3.48/1.00  
% 3.48/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.48/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/1.00  git: non_committed_changes: false
% 3.48/1.00  git: last_make_outside_of_git: false
% 3.48/1.00  
% 3.48/1.00  ------ 
% 3.48/1.00  ------ Parsing...
% 3.48/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  ------ Proving...
% 3.48/1.00  ------ Problem Properties 
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  clauses                                 27
% 3.48/1.00  conjectures                             2
% 3.48/1.00  EPR                                     4
% 3.48/1.00  Horn                                    24
% 3.48/1.00  unary                                   10
% 3.48/1.00  binary                                  10
% 3.48/1.00  lits                                    53
% 3.48/1.00  lits eq                                 8
% 3.48/1.00  fd_pure                                 0
% 3.48/1.00  fd_pseudo                               0
% 3.48/1.00  fd_cond                                 2
% 3.48/1.00  fd_pseudo_cond                          5
% 3.48/1.00  AC symbols                              0
% 3.48/1.00  
% 3.48/1.00  ------ Input Options Time Limit: Unbounded
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing...
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.48/1.00  Current options:
% 3.48/1.00  ------ 
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing...
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing...
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing...
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  % SZS status Theorem for theBenchmark.p
% 3.48/1.00  
% 3.48/1.00   Resolution empty clause
% 3.48/1.00  
% 3.48/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/1.00  
% 3.48/1.00  fof(f17,axiom,(
% 3.48/1.00    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f69,plain,(
% 3.48/1.00    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 3.48/1.00    inference(cnf_transformation,[],[f17])).
% 3.48/1.00  
% 3.48/1.00  fof(f1,axiom,(
% 3.48/1.00    v1_xboole_0(o_0_0_xboole_0)),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f44,plain,(
% 3.48/1.00    v1_xboole_0(o_0_0_xboole_0)),
% 3.48/1.00    inference(cnf_transformation,[],[f1])).
% 3.48/1.00  
% 3.48/1.00  fof(f5,axiom,(
% 3.48/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f26,plain,(
% 3.48/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f5])).
% 3.48/1.00  
% 3.48/1.00  fof(f50,plain,(
% 3.48/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f26])).
% 3.48/1.00  
% 3.48/1.00  fof(f18,axiom,(
% 3.48/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f29,plain,(
% 3.48/1.00    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/1.00    inference(ennf_transformation,[],[f18])).
% 3.48/1.00  
% 3.48/1.00  fof(f41,plain,(
% 3.48/1.00    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/1.00    inference(nnf_transformation,[],[f29])).
% 3.48/1.00  
% 3.48/1.00  fof(f71,plain,(
% 3.48/1.00    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/1.00    inference(cnf_transformation,[],[f41])).
% 3.48/1.00  
% 3.48/1.00  fof(f88,plain,(
% 3.48/1.00    ( ! [X0] : (r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) | ~m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.48/1.00    inference(equality_resolution,[],[f71])).
% 3.48/1.00  
% 3.48/1.00  fof(f16,axiom,(
% 3.48/1.00    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f68,plain,(
% 3.48/1.00    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.48/1.00    inference(cnf_transformation,[],[f16])).
% 3.48/1.00  
% 3.48/1.00  fof(f12,axiom,(
% 3.48/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f35,plain,(
% 3.48/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.48/1.00    inference(nnf_transformation,[],[f12])).
% 3.48/1.00  
% 3.48/1.00  fof(f36,plain,(
% 3.48/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.48/1.00    inference(rectify,[],[f35])).
% 3.48/1.00  
% 3.48/1.00  fof(f37,plain,(
% 3.48/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.48/1.00    introduced(choice_axiom,[])).
% 3.48/1.00  
% 3.48/1.00  fof(f38,plain,(
% 3.48/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.48/1.00  
% 3.48/1.00  fof(f58,plain,(
% 3.48/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.48/1.00    inference(cnf_transformation,[],[f38])).
% 3.48/1.00  
% 3.48/1.00  fof(f85,plain,(
% 3.48/1.00    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.48/1.00    inference(equality_resolution,[],[f58])).
% 3.48/1.00  
% 3.48/1.00  fof(f10,axiom,(
% 3.48/1.00    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f55,plain,(
% 3.48/1.00    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f10])).
% 3.48/1.00  
% 3.48/1.00  fof(f8,axiom,(
% 3.48/1.00    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f53,plain,(
% 3.48/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f8])).
% 3.48/1.00  
% 3.48/1.00  fof(f9,axiom,(
% 3.48/1.00    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f54,plain,(
% 3.48/1.00    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f9])).
% 3.48/1.00  
% 3.48/1.00  fof(f6,axiom,(
% 3.48/1.00    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f51,plain,(
% 3.48/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f6])).
% 3.48/1.00  
% 3.48/1.00  fof(f7,axiom,(
% 3.48/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f52,plain,(
% 3.48/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f7])).
% 3.48/1.00  
% 3.48/1.00  fof(f76,plain,(
% 3.48/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.48/1.00    inference(definition_unfolding,[],[f51,f52])).
% 3.48/1.00  
% 3.48/1.00  fof(f77,plain,(
% 3.48/1.00    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.48/1.00    inference(definition_unfolding,[],[f54,f76])).
% 3.48/1.00  
% 3.48/1.00  fof(f78,plain,(
% 3.48/1.00    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.48/1.00    inference(definition_unfolding,[],[f55,f53,f77])).
% 3.48/1.00  
% 3.48/1.00  fof(f20,axiom,(
% 3.48/1.00    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0))))))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f30,plain,(
% 3.48/1.00    ! [X0,X1] : (! [X2] : (! [X3] : ((m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f20])).
% 3.48/1.00  
% 3.48/1.00  fof(f31,plain,(
% 3.48/1.00    ! [X0,X1] : (! [X2] : (! [X3] : (m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 3.48/1.00    inference(flattening,[],[f30])).
% 3.48/1.00  
% 3.48/1.00  fof(f73,plain,(
% 3.48/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k1_enumset1(X1,X2,X3),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f31])).
% 3.48/1.00  
% 3.48/1.00  fof(f11,axiom,(
% 3.48/1.00    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f56,plain,(
% 3.48/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f11])).
% 3.48/1.00  
% 3.48/1.00  fof(f82,plain,(
% 3.48/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 3.48/1.00    inference(definition_unfolding,[],[f73,f56])).
% 3.48/1.00  
% 3.48/1.00  fof(f22,conjecture,(
% 3.48/1.00    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f23,negated_conjecture,(
% 3.48/1.00    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 3.48/1.00    inference(negated_conjecture,[],[f22])).
% 3.48/1.00  
% 3.48/1.00  fof(f34,plain,(
% 3.48/1.00    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 3.48/1.00    inference(ennf_transformation,[],[f23])).
% 3.48/1.00  
% 3.48/1.00  fof(f42,plain,(
% 3.48/1.00    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.48/1.00    introduced(choice_axiom,[])).
% 3.48/1.00  
% 3.48/1.00  fof(f43,plain,(
% 3.48/1.00    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f42])).
% 3.48/1.00  
% 3.48/1.00  fof(f75,plain,(
% 3.48/1.00    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.48/1.00    inference(cnf_transformation,[],[f43])).
% 3.48/1.00  
% 3.48/1.00  fof(f83,plain,(
% 3.48/1.00    ~m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.48/1.00    inference(definition_unfolding,[],[f75,f77])).
% 3.48/1.00  
% 3.48/1.00  fof(f19,axiom,(
% 3.48/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f72,plain,(
% 3.48/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.48/1.00    inference(cnf_transformation,[],[f19])).
% 3.48/1.00  
% 3.48/1.00  fof(f21,axiom,(
% 3.48/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f32,plain,(
% 3.48/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.48/1.00    inference(ennf_transformation,[],[f21])).
% 3.48/1.00  
% 3.48/1.00  fof(f33,plain,(
% 3.48/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.48/1.00    inference(flattening,[],[f32])).
% 3.48/1.00  
% 3.48/1.00  fof(f74,plain,(
% 3.48/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f33])).
% 3.48/1.00  
% 3.48/1.00  fof(f4,axiom,(
% 3.48/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f49,plain,(
% 3.48/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.48/1.00    inference(cnf_transformation,[],[f4])).
% 3.48/1.00  
% 3.48/1.00  fof(f3,axiom,(
% 3.48/1.00    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f25,plain,(
% 3.48/1.00    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.48/1.00    inference(ennf_transformation,[],[f3])).
% 3.48/1.00  
% 3.48/1.00  fof(f48,plain,(
% 3.48/1.00    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 3.48/1.00    inference(cnf_transformation,[],[f25])).
% 3.48/1.00  
% 3.48/1.00  fof(f15,axiom,(
% 3.48/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f39,plain,(
% 3.48/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.48/1.00    inference(nnf_transformation,[],[f15])).
% 3.48/1.00  
% 3.48/1.00  fof(f40,plain,(
% 3.48/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.48/1.00    inference(flattening,[],[f39])).
% 3.48/1.00  
% 3.48/1.00  fof(f66,plain,(
% 3.48/1.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.48/1.00    inference(cnf_transformation,[],[f40])).
% 3.48/1.00  
% 3.48/1.00  fof(f80,plain,(
% 3.48/1.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))) )),
% 3.48/1.00    inference(definition_unfolding,[],[f66,f77])).
% 3.48/1.00  
% 3.48/1.00  fof(f87,plain,(
% 3.48/1.00    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))) )),
% 3.48/1.00    inference(equality_resolution,[],[f80])).
% 3.48/1.00  
% 3.48/1.00  fof(f14,axiom,(
% 3.48/1.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f28,plain,(
% 3.48/1.00    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 3.48/1.00    inference(ennf_transformation,[],[f14])).
% 3.48/1.00  
% 3.48/1.00  fof(f63,plain,(
% 3.48/1.00    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f28])).
% 3.48/1.00  
% 3.48/1.00  fof(f13,axiom,(
% 3.48/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f27,plain,(
% 3.48/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.48/1.00    inference(ennf_transformation,[],[f13])).
% 3.48/1.00  
% 3.48/1.00  fof(f62,plain,(
% 3.48/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f27])).
% 3.48/1.00  
% 3.48/1.00  fof(f59,plain,(
% 3.48/1.00    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f38])).
% 3.48/1.00  
% 3.48/1.00  fof(f2,axiom,(
% 3.48/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.48/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f24,plain,(
% 3.48/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.48/1.00    inference(ennf_transformation,[],[f2])).
% 3.48/1.00  
% 3.48/1.00  fof(f45,plain,(
% 3.48/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.48/1.00    inference(cnf_transformation,[],[f24])).
% 3.48/1.00  
% 3.48/1.00  cnf(c_20,plain,
% 3.48/1.00      ( v1_xboole_0(k1_subset_1(X0)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4068,plain,
% 3.48/1.00      ( v1_xboole_0(k1_subset_1(X0)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_0,plain,
% 3.48/1.00      ( v1_xboole_0(o_0_0_xboole_0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4087,plain,
% 3.48/1.00      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_6,plain,
% 3.48/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.48/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4081,plain,
% 3.48/1.00      ( X0 = X1
% 3.48/1.00      | v1_xboole_0(X0) != iProver_top
% 3.48/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4412,plain,
% 3.48/1.00      ( o_0_0_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4087,c_4081]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4553,plain,
% 3.48/1.00      ( k1_subset_1(X0) = o_0_0_xboole_0 ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4068,c_4412]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_21,plain,
% 3.48/1.00      ( ~ m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))
% 3.48/1.00      | r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) ),
% 3.48/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_19,plain,
% 3.48/1.00      ( m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_151,plain,
% 3.48/1.00      ( r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) ),
% 3.48/1.00      inference(global_propositional_subsumption,[status(thm)],[c_21,c_19]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4062,plain,
% 3.48/1.00      ( r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4578,plain,
% 3.48/1.00      ( r1_tarski(o_0_0_xboole_0,k3_subset_1(X0,o_0_0_xboole_0)) = iProver_top ),
% 3.48/1.00      inference(demodulation,[status(thm)],[c_4553,c_4062]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_10,plain,
% 3.48/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.48/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4078,plain,
% 3.48/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.48/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_7,plain,
% 3.48/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_24,plain,
% 3.48/1.00      ( ~ m1_subset_1(X0,X1)
% 3.48/1.00      | ~ m1_subset_1(X2,X1)
% 3.48/1.00      | ~ m1_subset_1(X3,X1)
% 3.48/1.00      | m1_subset_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X0),k1_zfmisc_1(X1))
% 3.48/1.00      | k1_xboole_0 = X1 ),
% 3.48/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4065,plain,
% 3.48/1.00      ( k1_xboole_0 = X0
% 3.48/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.48/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.48/1.00      | m1_subset_1(X3,X0) != iProver_top
% 3.48/1.00      | m1_subset_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4725,plain,
% 3.48/1.00      ( k1_xboole_0 = X0
% 3.48/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.48/1.00      | m1_subset_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_7,c_4065]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_26,negated_conjecture,
% 3.48/1.00      ( ~ m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.48/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4063,plain,
% 3.48/1.00      ( m1_subset_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5063,plain,
% 3.48/1.00      ( k1_zfmisc_1(sK1) = k1_xboole_0
% 3.48/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4725,c_4063]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_23,plain,
% 3.48/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4066,plain,
% 3.48/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5088,plain,
% 3.48/1.00      ( k1_zfmisc_1(sK1) = k1_xboole_0 ),
% 3.48/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5063,c_4066]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_25,plain,
% 3.48/1.00      ( m1_subset_1(X0,X1)
% 3.48/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.48/1.00      | ~ r2_hidden(X0,X2) ),
% 3.48/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4064,plain,
% 3.48/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.48/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.48/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5095,plain,
% 3.48/1.00      ( m1_subset_1(X0,sK1) = iProver_top
% 3.48/1.00      | m1_subset_1(X1,k1_xboole_0) != iProver_top
% 3.48/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_5088,c_4064]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5232,plain,
% 3.48/1.00      ( m1_subset_1(X0,sK1) = iProver_top
% 3.48/1.00      | m1_subset_1(k1_zfmisc_1(X1),k1_xboole_0) != iProver_top
% 3.48/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4078,c_5095]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5,plain,
% 3.48/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4082,plain,
% 3.48/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_3,plain,
% 3.48/1.00      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 3.48/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4084,plain,
% 3.48/1.00      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4340,plain,
% 3.48/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4082,c_4084]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_17,negated_conjecture,
% 3.48/1.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) ),
% 3.48/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4071,plain,
% 3.48/1.00      ( r2_hidden(X0,k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4365,plain,
% 3.48/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4340,c_4071]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4372,plain,
% 3.48/1.00      ( r2_hidden(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(instantiation,[status(thm)],[c_4365]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_15,plain,
% 3.48/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.48/1.00      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4073,plain,
% 3.48/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.48/1.00      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4465,plain,
% 3.48/1.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X0) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4073,c_4084]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4621,plain,
% 3.48/1.00      ( k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k1_xboole_0 ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4082,c_4465]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4633,plain,
% 3.48/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.48/1.00      inference(light_normalisation,[status(thm)],[c_4621,c_4340]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12,plain,
% 3.48/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4076,plain,
% 3.48/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.48/1.00      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4645,plain,
% 3.48/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.48/1.00      | r1_tarski(k2_zfmisc_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4633,c_4076]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4668,plain,
% 3.48/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.48/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.48/1.00      inference(light_normalisation,[status(thm)],[c_4645,c_4633]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_9,plain,
% 3.48/1.00      ( r2_hidden(sK0(X0,X1),X1)
% 3.48/1.00      | r1_tarski(sK0(X0,X1),X0)
% 3.48/1.00      | k1_zfmisc_1(X0) = X1 ),
% 3.48/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4079,plain,
% 3.48/1.00      ( k1_zfmisc_1(X0) = X1
% 3.48/1.00      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.48/1.00      | r1_tarski(sK0(X0,X1),X0) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4756,plain,
% 3.48/1.00      ( k1_zfmisc_1(X0) = k1_xboole_0
% 3.48/1.00      | r1_tarski(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4079,c_4365]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_2,plain,
% 3.48/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4085,plain,
% 3.48/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.48/1.00      | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4389,plain,
% 3.48/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.48/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4340,c_4085]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4854,plain,
% 3.48/1.00      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
% 3.48/1.00      | r1_tarski(sK0(k1_xboole_0,k1_xboole_0),X0) = iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4756,c_4389]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5096,plain,
% 3.48/1.00      ( r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.48/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_5088,c_4078]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5182,plain,
% 3.48/1.00      ( r1_tarski(X0,sK1) != iProver_top ),
% 3.48/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5096,c_4365]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5193,plain,
% 3.48/1.00      ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4854,c_5182]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5566,plain,
% 3.48/1.00      ( r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.48/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_5193,c_4078]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5580,plain,
% 3.48/1.00      ( r2_hidden(k1_xboole_0,k1_xboole_0) = iProver_top
% 3.48/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(instantiation,[status(thm)],[c_5566]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5655,plain,
% 3.48/1.00      ( r1_tarski(X0,X1) != iProver_top ),
% 3.48/1.00      inference(global_propositional_subsumption,
% 3.48/1.00                [status(thm)],
% 3.48/1.00                [c_5232,c_4372,c_4668,c_5580]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5663,plain,
% 3.48/1.00      ( $false ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_4578,c_5655]) ).
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/1.00  
% 3.48/1.00  ------                               Statistics
% 3.48/1.00  
% 3.48/1.00  ------ Selected
% 3.48/1.00  
% 3.48/1.00  total_time:                             0.164
% 3.48/1.00  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:46:04 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 181 expanded)
%              Number of clauses        :   34 (  52 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  200 ( 311 expanded)
%              Number of equality atoms :   82 ( 187 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0] :
      ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f31])).

fof(f57,plain,(
    k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f43,f62,f62,f62])).

fof(f68,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f25])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6851,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_16])).

cnf(c_172,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2445,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_172,c_0])).

cnf(c_169,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6166,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2445,c_169])).

cnf(c_4,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_516,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_0,c_1])).

cnf(c_573,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4,c_516])).

cnf(c_170,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_782,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_170,c_169])).

cnf(c_791,plain,
    ( X0 = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_782,c_1])).

cnf(c_798,plain,
    ( X0 = X1
    | X1 != k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_791,c_170])).

cnf(c_1055,plain,
    ( X0 = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_798,c_1])).

cnf(c_1064,plain,
    ( X0 = X1
    | X1 != k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1055,c_170])).

cnf(c_781,plain,
    ( X0 != X1
    | k4_xboole_0(X1,k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_170,c_1])).

cnf(c_1058,plain,
    ( X0 = k4_xboole_0(X1,k1_xboole_0)
    | k4_xboole_0(X0,k1_xboole_0) != X1 ),
    inference(resolution,[status(thm)],[c_798,c_781])).

cnf(c_3116,plain,
    ( X0 != X1
    | X1 = k4_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1058,c_781])).

cnf(c_4021,plain,
    ( X0 = X1
    | k4_xboole_0(X0,k1_xboole_0) != X1 ),
    inference(resolution,[status(thm)],[c_1064,c_3116])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4035,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4021,c_5])).

cnf(c_6633,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6166,c_573,c_4035])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6650,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_6633,c_13])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_928,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_11])).

cnf(c_7362,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(k9_relat_1(X0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6650,c_928])).

cnf(c_7629,plain,
    ( ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_6851,c_7362])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7629,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.64/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.99  
% 3.64/0.99  ------  iProver source info
% 3.64/0.99  
% 3.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.99  git: non_committed_changes: false
% 3.64/0.99  git: last_make_outside_of_git: false
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  ------ Parsing...
% 3.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  ------ Proving...
% 3.64/0.99  ------ Problem Properties 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  clauses                                 18
% 3.64/0.99  conjectures                             2
% 3.64/0.99  EPR                                     6
% 3.64/0.99  Horn                                    15
% 3.64/0.99  unary                                   6
% 3.64/0.99  binary                                  4
% 3.64/0.99  lits                                    40
% 3.64/0.99  lits eq                                 9
% 3.64/0.99  fd_pure                                 0
% 3.64/0.99  fd_pseudo                               0
% 3.64/0.99  fd_cond                                 1
% 3.64/0.99  fd_pseudo_cond                          1
% 3.64/0.99  AC symbols                              0
% 3.64/0.99  
% 3.64/0.99  ------ Input Options Time Limit: Unbounded
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  Current options:
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS status Theorem for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  fof(f4,axiom,(
% 3.64/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f18,plain,(
% 3.64/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.64/0.99    inference(ennf_transformation,[],[f4])).
% 3.64/0.99  
% 3.64/0.99  fof(f36,plain,(
% 3.64/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f18])).
% 3.64/0.99  
% 3.64/0.99  fof(f16,conjecture,(
% 3.64/0.99    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f17,negated_conjecture,(
% 3.64/0.99    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 3.64/0.99    inference(negated_conjecture,[],[f16])).
% 3.64/0.99  
% 3.64/0.99  fof(f21,plain,(
% 3.64/0.99    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 3.64/0.99    inference(ennf_transformation,[],[f17])).
% 3.64/0.99  
% 3.64/0.99  fof(f31,plain,(
% 3.64/0.99    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) & v1_relat_1(sK2))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f32,plain,(
% 3.64/0.99    k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) & v1_relat_1(sK2)),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f57,plain,(
% 3.64/0.99    k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)),
% 3.64/0.99    inference(cnf_transformation,[],[f32])).
% 3.64/0.99  
% 3.64/0.99  fof(f1,axiom,(
% 3.64/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f33,plain,(
% 3.64/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f1])).
% 3.64/0.99  
% 3.64/0.99  fof(f3,axiom,(
% 3.64/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f35,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.64/0.99    inference(cnf_transformation,[],[f3])).
% 3.64/0.99  
% 3.64/0.99  fof(f63,plain,(
% 3.64/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.64/0.99    inference(definition_unfolding,[],[f33,f35])).
% 3.64/0.99  
% 3.64/0.99  fof(f11,axiom,(
% 3.64/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f22,plain,(
% 3.64/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.64/0.99    inference(nnf_transformation,[],[f11])).
% 3.64/0.99  
% 3.64/0.99  fof(f43,plain,(
% 3.64/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f22])).
% 3.64/0.99  
% 3.64/0.99  fof(f5,axiom,(
% 3.64/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f37,plain,(
% 3.64/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f5])).
% 3.64/0.99  
% 3.64/0.99  fof(f6,axiom,(
% 3.64/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f38,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f6])).
% 3.64/0.99  
% 3.64/0.99  fof(f10,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f42,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f7,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f39,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f7])).
% 3.64/0.99  
% 3.64/0.99  fof(f8,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f40,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f8])).
% 3.64/0.99  
% 3.64/0.99  fof(f9,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f41,plain,(
% 3.64/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f9])).
% 3.64/0.99  
% 3.64/0.99  fof(f58,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f40,f41])).
% 3.64/0.99  
% 3.64/0.99  fof(f59,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f39,f58])).
% 3.64/0.99  
% 3.64/0.99  fof(f60,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f42,f59])).
% 3.64/0.99  
% 3.64/0.99  fof(f61,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f38,f60])).
% 3.64/0.99  
% 3.64/0.99  fof(f62,plain,(
% 3.64/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f37,f61])).
% 3.64/0.99  
% 3.64/0.99  fof(f65,plain,(
% 3.64/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f43,f62,f62,f62])).
% 3.64/0.99  
% 3.64/0.99  fof(f68,plain,(
% 3.64/0.99    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.64/0.99    inference(equality_resolution,[],[f65])).
% 3.64/0.99  
% 3.64/0.99  fof(f2,axiom,(
% 3.64/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f34,plain,(
% 3.64/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.64/0.99    inference(cnf_transformation,[],[f2])).
% 3.64/0.99  
% 3.64/0.99  fof(f12,axiom,(
% 3.64/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f23,plain,(
% 3.64/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 3.64/0.99    inference(nnf_transformation,[],[f12])).
% 3.64/0.99  
% 3.64/0.99  fof(f46,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f23])).
% 3.64/0.99  
% 3.64/0.99  fof(f66,plain,(
% 3.64/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.64/0.99    inference(definition_unfolding,[],[f46,f62])).
% 3.64/0.99  
% 3.64/0.99  fof(f15,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f20,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.64/0.99    inference(ennf_transformation,[],[f15])).
% 3.64/0.99  
% 3.64/0.99  fof(f27,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.64/0.99    inference(nnf_transformation,[],[f20])).
% 3.64/0.99  
% 3.64/0.99  fof(f28,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.64/0.99    inference(rectify,[],[f27])).
% 3.64/0.99  
% 3.64/0.99  fof(f29,plain,(
% 3.64/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f30,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.64/0.99  
% 3.64/0.99  fof(f54,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f30])).
% 3.64/0.99  
% 3.64/0.99  fof(f13,axiom,(
% 3.64/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f19,plain,(
% 3.64/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f13])).
% 3.64/0.99  
% 3.64/0.99  fof(f24,plain,(
% 3.64/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.64/0.99    inference(nnf_transformation,[],[f19])).
% 3.64/0.99  
% 3.64/0.99  fof(f47,plain,(
% 3.64/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f24])).
% 3.64/0.99  
% 3.64/0.99  fof(f14,axiom,(
% 3.64/0.99    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f25,plain,(
% 3.64/0.99    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f26,plain,(
% 3.64/0.99    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f25])).
% 3.64/0.99  
% 3.64/0.99  fof(f51,plain,(
% 3.64/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f26])).
% 3.64/0.99  
% 3.64/0.99  fof(f56,plain,(
% 3.64/0.99    v1_relat_1(sK2)),
% 3.64/0.99    inference(cnf_transformation,[],[f32])).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2,plain,
% 3.64/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_16,negated_conjecture,
% 3.64/0.99      ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6851,plain,
% 3.64/0.99      ( ~ v1_xboole_0(k9_relat_1(sK2,k1_xboole_0)) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_2,c_16]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_172,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.64/0.99      theory(equality) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_0,plain,
% 3.64/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2445,plain,
% 3.64/0.99      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
% 3.64/0.99      | ~ r2_hidden(X2,k1_xboole_0)
% 3.64/0.99      | X0 != X2 ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_172,c_0]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_169,plain,( X0 = X0 ),theory(equality) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6166,plain,
% 3.64/0.99      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
% 3.64/0.99      | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_2445,c_169]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4,plain,
% 3.64/0.99      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1,plain,
% 3.64/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_516,plain,
% 3.64/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.64/0.99      inference(light_normalisation,[status(thm)],[c_0,c_1]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_573,plain,
% 3.64/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 3.64/0.99      inference(demodulation,[status(thm)],[c_4,c_516]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_170,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_782,plain,
% 3.64/0.99      ( X0 != X1 | X1 = X0 ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_170,c_169]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_791,plain,
% 3.64/0.99      ( X0 = k4_xboole_0(X0,k1_xboole_0) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_782,c_1]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_798,plain,
% 3.64/0.99      ( X0 = X1 | X1 != k4_xboole_0(X0,k1_xboole_0) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_791,c_170]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1055,plain,
% 3.64/0.99      ( X0 = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_798,c_1]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1064,plain,
% 3.64/0.99      ( X0 = X1
% 3.64/0.99      | X1 != k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_1055,c_170]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_781,plain,
% 3.64/0.99      ( X0 != X1 | k4_xboole_0(X1,k1_xboole_0) = X0 ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_170,c_1]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1058,plain,
% 3.64/0.99      ( X0 = k4_xboole_0(X1,k1_xboole_0)
% 3.64/0.99      | k4_xboole_0(X0,k1_xboole_0) != X1 ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_798,c_781]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3116,plain,
% 3.64/0.99      ( X0 != X1 | X1 = k4_xboole_0(X0,k1_xboole_0) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_1058,c_781]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4021,plain,
% 3.64/0.99      ( X0 = X1 | k4_xboole_0(X0,k1_xboole_0) != X1 ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_1064,c_3116]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,X1)
% 3.64/0.99      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0 ),
% 3.64/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4035,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,k1_xboole_0)
% 3.64/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0 ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_4021,c_5]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6633,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_6166,c_573,c_4035]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_13,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.64/0.99      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.64/0.99      | ~ v1_relat_1(X1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6650,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,k1_xboole_0)) | ~ v1_relat_1(X1) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_6633,c_13]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_10,plain,
% 3.64/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_11,plain,
% 3.64/0.99      ( m1_subset_1(sK0(X0),X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_928,plain,
% 3.64/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_10,c_11]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7362,plain,
% 3.64/0.99      ( ~ v1_relat_1(X0) | v1_xboole_0(k9_relat_1(X0,k1_xboole_0)) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_6650,c_928]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7629,plain,
% 3.64/0.99      ( ~ v1_relat_1(sK2) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_6851,c_7362]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_17,negated_conjecture,
% 3.64/0.99      ( v1_relat_1(sK2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(contradiction,plain,
% 3.64/0.99      ( $false ),
% 3.64/0.99      inference(minisat,[status(thm)],[c_7629,c_17]) ).
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  ------                               Statistics
% 3.64/0.99  
% 3.64/0.99  ------ Selected
% 3.64/0.99  
% 3.64/0.99  total_time:                             0.292
% 3.64/0.99  
%------------------------------------------------------------------------------

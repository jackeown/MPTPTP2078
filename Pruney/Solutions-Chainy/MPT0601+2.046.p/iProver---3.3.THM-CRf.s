%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:27 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 113 expanded)
%              Number of clauses        :   34 (  39 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  220 ( 394 expanded)
%              Number of equality atoms :   46 (  93 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).

fof(f31,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK5,sK4)
        | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
      & ( k1_xboole_0 != k11_relat_1(sK5,sK4)
        | r2_hidden(sK4,k1_relat_1(sK5)) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK5,sK4)
      | ~ r2_hidden(sK4,k1_relat_1(sK5)) )
    & ( k1_xboole_0 != k11_relat_1(sK5,sK4)
      | r2_hidden(sK4,k1_relat_1(sK5)) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f24])).

fof(f36,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,
    ( k1_xboole_0 = k11_relat_1(sK5,sK4)
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,
    ( k1_xboole_0 != k11_relat_1(sK5,sK4)
    | r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_182,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_183,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_4911,plain,
    ( ~ r2_hidden(sK3(sK5,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_340,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_939,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | X1 != k11_relat_1(sK5,sK4)
    | X0 != sK3(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_2134,plain,
    ( r2_hidden(sK3(sK5,sK4),X0)
    | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | X0 != k11_relat_1(sK5,sK4)
    | sK3(sK5,sK4) != sK3(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_4365,plain,
    ( ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | r2_hidden(sK3(sK5,sK4),k1_xboole_0)
    | sK3(sK5,sK4) != sK3(sK5,sK4)
    | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_338,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2135,plain,
    ( sK3(sK5,sK4) = sK3(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1276,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK0(k11_relat_1(sK5,sK4),k1_xboole_0)),sK5)
    | r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_205,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_206,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_266,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK5)
    | ~ r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_206])).

cnf(c_267,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_824,plain,
    ( r2_hidden(k4_tarski(sK4,sK0(k11_relat_1(sK5,sK4),k1_xboole_0)),sK5)
    | ~ r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k11_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_9,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_193,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_194,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_268,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK5)
    | r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_194])).

cnf(c_269,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_805,plain,
    ( r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | ~ r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_794,plain,
    ( r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5)
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_765,plain,
    ( ~ r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_757,plain,
    ( r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k11_relat_1(sK5,sK4))
    | r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(sK4,k1_relat_1(sK5))
    | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK4,k1_relat_1(sK5))
    | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4911,c_4365,c_2135,c_1276,c_824,c_805,c_794,c_765,c_757,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.40/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.00  
% 2.40/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/1.00  
% 2.40/1.00  ------  iProver source info
% 2.40/1.00  
% 2.40/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.40/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/1.00  git: non_committed_changes: false
% 2.40/1.00  git: last_make_outside_of_git: false
% 2.40/1.00  
% 2.40/1.00  ------ 
% 2.40/1.00  ------ Parsing...
% 2.40/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/1.00  
% 2.40/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.40/1.00  
% 2.40/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/1.00  
% 2.40/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/1.00  ------ Proving...
% 2.40/1.00  ------ Problem Properties 
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  clauses                                 11
% 2.40/1.00  conjectures                             2
% 2.40/1.00  EPR                                     1
% 2.40/1.00  Horn                                    9
% 2.40/1.00  unary                                   1
% 2.40/1.00  binary                                  6
% 2.40/1.00  lits                                    25
% 2.40/1.00  lits eq                                 6
% 2.40/1.00  fd_pure                                 0
% 2.40/1.00  fd_pseudo                               0
% 2.40/1.00  fd_cond                                 0
% 2.40/1.00  fd_pseudo_cond                          4
% 2.40/1.00  AC symbols                              0
% 2.40/1.00  
% 2.40/1.00  ------ Input Options Time Limit: Unbounded
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  ------ 
% 2.40/1.00  Current options:
% 2.40/1.00  ------ 
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  ------ Proving...
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  % SZS status Theorem for theBenchmark.p
% 2.40/1.00  
% 2.40/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/1.00  
% 2.40/1.00  fof(f1,axiom,(
% 2.40/1.00    v1_xboole_0(k1_xboole_0)),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f26,plain,(
% 2.40/1.00    v1_xboole_0(k1_xboole_0)),
% 2.40/1.00    inference(cnf_transformation,[],[f1])).
% 2.40/1.00  
% 2.40/1.00  fof(f3,axiom,(
% 2.40/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f9,plain,(
% 2.40/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 2.40/1.00    inference(ennf_transformation,[],[f3])).
% 2.40/1.00  
% 2.40/1.00  fof(f29,plain,(
% 2.40/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f9])).
% 2.40/1.00  
% 2.40/1.00  fof(f4,axiom,(
% 2.40/1.00    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f15,plain,(
% 2.40/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.40/1.00    inference(nnf_transformation,[],[f4])).
% 2.40/1.00  
% 2.40/1.00  fof(f16,plain,(
% 2.40/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.40/1.00    inference(rectify,[],[f15])).
% 2.40/1.00  
% 2.40/1.00  fof(f19,plain,(
% 2.40/1.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.40/1.00    introduced(choice_axiom,[])).
% 2.40/1.00  
% 2.40/1.00  fof(f18,plain,(
% 2.40/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.40/1.00    introduced(choice_axiom,[])).
% 2.40/1.00  
% 2.40/1.00  fof(f17,plain,(
% 2.40/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.40/1.00    introduced(choice_axiom,[])).
% 2.40/1.00  
% 2.40/1.00  fof(f20,plain,(
% 2.40/1.00    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 2.40/1.00  
% 2.40/1.00  fof(f31,plain,(
% 2.40/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.40/1.00    inference(cnf_transformation,[],[f20])).
% 2.40/1.00  
% 2.40/1.00  fof(f39,plain,(
% 2.40/1.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.40/1.00    inference(equality_resolution,[],[f31])).
% 2.40/1.00  
% 2.40/1.00  fof(f5,axiom,(
% 2.40/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f10,plain,(
% 2.40/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.40/1.00    inference(ennf_transformation,[],[f5])).
% 2.40/1.00  
% 2.40/1.00  fof(f21,plain,(
% 2.40/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.40/1.00    inference(nnf_transformation,[],[f10])).
% 2.40/1.00  
% 2.40/1.00  fof(f35,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f21])).
% 2.40/1.00  
% 2.40/1.00  fof(f6,conjecture,(
% 2.40/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f7,negated_conjecture,(
% 2.40/1.00    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.40/1.00    inference(negated_conjecture,[],[f6])).
% 2.40/1.00  
% 2.40/1.00  fof(f11,plain,(
% 2.40/1.00    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 2.40/1.00    inference(ennf_transformation,[],[f7])).
% 2.40/1.00  
% 2.40/1.00  fof(f22,plain,(
% 2.40/1.00    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 2.40/1.00    inference(nnf_transformation,[],[f11])).
% 2.40/1.00  
% 2.40/1.00  fof(f23,plain,(
% 2.40/1.00    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.40/1.00    inference(flattening,[],[f22])).
% 2.40/1.00  
% 2.40/1.00  fof(f24,plain,(
% 2.40/1.00    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))) & (k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))) & v1_relat_1(sK5))),
% 2.40/1.00    introduced(choice_axiom,[])).
% 2.40/1.00  
% 2.40/1.00  fof(f25,plain,(
% 2.40/1.00    (k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))) & (k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))) & v1_relat_1(sK5)),
% 2.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f24])).
% 2.40/1.00  
% 2.40/1.00  fof(f36,plain,(
% 2.40/1.00    v1_relat_1(sK5)),
% 2.40/1.00    inference(cnf_transformation,[],[f25])).
% 2.40/1.00  
% 2.40/1.00  fof(f34,plain,(
% 2.40/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f21])).
% 2.40/1.00  
% 2.40/1.00  fof(f30,plain,(
% 2.40/1.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.40/1.00    inference(cnf_transformation,[],[f20])).
% 2.40/1.00  
% 2.40/1.00  fof(f40,plain,(
% 2.40/1.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.40/1.00    inference(equality_resolution,[],[f30])).
% 2.40/1.00  
% 2.40/1.00  fof(f2,axiom,(
% 2.40/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.00  
% 2.40/1.00  fof(f8,plain,(
% 2.40/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.40/1.00    inference(ennf_transformation,[],[f2])).
% 2.40/1.00  
% 2.40/1.00  fof(f12,plain,(
% 2.40/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.40/1.00    inference(nnf_transformation,[],[f8])).
% 2.40/1.00  
% 2.40/1.00  fof(f13,plain,(
% 2.40/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.40/1.00    introduced(choice_axiom,[])).
% 2.40/1.00  
% 2.40/1.00  fof(f14,plain,(
% 2.40/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 2.40/1.00  
% 2.40/1.00  fof(f27,plain,(
% 2.40/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.40/1.00    inference(cnf_transformation,[],[f14])).
% 2.40/1.00  
% 2.40/1.00  fof(f38,plain,(
% 2.40/1.00    k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))),
% 2.40/1.00    inference(cnf_transformation,[],[f25])).
% 2.40/1.00  
% 2.40/1.00  fof(f37,plain,(
% 2.40/1.00    k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))),
% 2.40/1.00    inference(cnf_transformation,[],[f25])).
% 2.40/1.00  
% 2.40/1.00  cnf(c_0,plain,
% 2.40/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_182,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_183,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_182]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4911,plain,
% 2.40/1.00      ( ~ r2_hidden(sK3(sK5,sK4),k1_xboole_0) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_183]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_340,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.40/1.00      theory(equality) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_939,plain,
% 2.40/1.00      ( r2_hidden(X0,X1)
% 2.40/1.00      | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.40/1.00      | X1 != k11_relat_1(sK5,sK4)
% 2.40/1.00      | X0 != sK3(sK5,sK4) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_340]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2134,plain,
% 2.40/1.00      ( r2_hidden(sK3(sK5,sK4),X0)
% 2.40/1.00      | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.40/1.00      | X0 != k11_relat_1(sK5,sK4)
% 2.40/1.00      | sK3(sK5,sK4) != sK3(sK5,sK4) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_939]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4365,plain,
% 2.40/1.00      ( ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.40/1.00      | r2_hidden(sK3(sK5,sK4),k1_xboole_0)
% 2.40/1.00      | sK3(sK5,sK4) != sK3(sK5,sK4)
% 2.40/1.00      | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_2134]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_338,plain,( X0 = X0 ),theory(equality) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2135,plain,
% 2.40/1.00      ( sK3(sK5,sK4) = sK3(sK5,sK4) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_338]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_6,plain,
% 2.40/1.00      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1276,plain,
% 2.40/1.00      ( ~ r2_hidden(k4_tarski(sK4,sK0(k11_relat_1(sK5,sK4),k1_xboole_0)),sK5)
% 2.40/1.00      | r2_hidden(sK4,k1_relat_1(sK5)) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_8,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.40/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.40/1.00      | ~ v1_relat_1(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_12,negated_conjecture,
% 2.40/1.00      ( v1_relat_1(sK5) ),
% 2.40/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_205,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.40/1.00      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.40/1.00      | sK5 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_206,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
% 2.40/1.00      | r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_205]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_266,plain,
% 2.40/1.00      ( r2_hidden(k4_tarski(X1,X0),sK5)
% 2.40/1.00      | ~ r2_hidden(X0,k11_relat_1(sK5,X1)) ),
% 2.40/1.00      inference(prop_impl,[status(thm)],[c_206]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_267,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
% 2.40/1.00      | r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_266]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_824,plain,
% 2.40/1.00      ( r2_hidden(k4_tarski(sK4,sK0(k11_relat_1(sK5,sK4),k1_xboole_0)),sK5)
% 2.40/1.00      | ~ r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k11_relat_1(sK5,sK4)) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_267]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_9,plain,
% 2.40/1.00      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.40/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.40/1.00      | ~ v1_relat_1(X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_193,plain,
% 2.40/1.00      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.40/1.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.40/1.00      | sK5 != X1 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_194,plain,
% 2.40/1.00      ( r2_hidden(X0,k11_relat_1(sK5,X1))
% 2.40/1.00      | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_193]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_268,plain,
% 2.40/1.00      ( ~ r2_hidden(k4_tarski(X1,X0),sK5)
% 2.40/1.00      | r2_hidden(X0,k11_relat_1(sK5,X1)) ),
% 2.40/1.00      inference(prop_impl,[status(thm)],[c_194]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_269,plain,
% 2.40/1.00      ( r2_hidden(X0,k11_relat_1(sK5,X1))
% 2.40/1.00      | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.40/1.00      inference(renaming,[status(thm)],[c_268]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_805,plain,
% 2.40/1.00      ( r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.40/1.00      | ~ r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_269]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_7,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.40/1.00      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_794,plain,
% 2.40/1.00      ( r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5)
% 2.40/1.00      | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_765,plain,
% 2.40/1.00      ( ~ r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_183]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2,plain,
% 2.40/1.00      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.40/1.00      inference(cnf_transformation,[],[f27]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_757,plain,
% 2.40/1.00      ( r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k11_relat_1(sK5,sK4))
% 2.40/1.00      | r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
% 2.40/1.00      | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_10,negated_conjecture,
% 2.40/1.00      ( ~ r2_hidden(sK4,k1_relat_1(sK5))
% 2.40/1.00      | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
% 2.40/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_11,negated_conjecture,
% 2.40/1.00      ( r2_hidden(sK4,k1_relat_1(sK5))
% 2.40/1.00      | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
% 2.40/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(contradiction,plain,
% 2.40/1.00      ( $false ),
% 2.40/1.00      inference(minisat,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_4911,c_4365,c_2135,c_1276,c_824,c_805,c_794,c_765,
% 2.40/1.00                 c_757,c_10,c_11]) ).
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/1.00  
% 2.40/1.00  ------                               Statistics
% 2.40/1.00  
% 2.40/1.00  ------ Selected
% 2.40/1.00  
% 2.40/1.00  total_time:                             0.165
% 2.40/1.00  
%------------------------------------------------------------------------------

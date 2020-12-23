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
% DateTime   : Thu Dec  3 11:48:28 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 113 expanded)
%              Number of clauses        :   34 (  39 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 ( 396 expanded)
%              Number of equality atoms :   47 (  95 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

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

fof(f26,plain,(
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

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_184,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_tarski(X0) != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_4912,plain,
    ( ~ r2_hidden(sK3(sK5,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_342,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_941,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | X1 != k11_relat_1(sK5,sK4)
    | X0 != sK3(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_2136,plain,
    ( r2_hidden(sK3(sK5,sK4),X0)
    | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | X0 != k11_relat_1(sK5,sK4)
    | sK3(sK5,sK4) != sK3(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_4366,plain,
    ( ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | r2_hidden(sK3(sK5,sK4),k1_xboole_0)
    | sK3(sK5,sK4) != sK3(sK5,sK4)
    | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_2136])).

cnf(c_340,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2137,plain,
    ( sK3(sK5,sK4) = sK3(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1278,plain,
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

cnf(c_207,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_208,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_268,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK5)
    | ~ r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_208])).

cnf(c_269,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
    | r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_826,plain,
    ( r2_hidden(k4_tarski(sK4,sK0(k11_relat_1(sK5,sK4),k1_xboole_0)),sK5)
    | ~ r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k11_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_9,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_195,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_196,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_270,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK5)
    | r2_hidden(X0,k11_relat_1(sK5,X1)) ),
    inference(prop_impl,[status(thm)],[c_196])).

cnf(c_271,plain,
    ( r2_hidden(X0,k11_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_807,plain,
    ( r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
    | ~ r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_796,plain,
    ( r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5)
    | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_767,plain,
    ( ~ r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_759,plain,
    ( r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k11_relat_1(sK5,sK4))
    | r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

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
    inference(minisat,[status(thm)],[c_4912,c_4366,c_2137,c_1278,c_826,c_807,c_796,c_767,c_759,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:57:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.94/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.04  
% 2.94/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.94/1.04  
% 2.94/1.04  ------  iProver source info
% 2.94/1.04  
% 2.94/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.94/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.94/1.04  git: non_committed_changes: false
% 2.94/1.04  git: last_make_outside_of_git: false
% 2.94/1.04  
% 2.94/1.04  ------ 
% 2.94/1.04  ------ Parsing...
% 2.94/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.94/1.04  
% 2.94/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.94/1.04  
% 2.94/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.94/1.04  
% 2.94/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.94/1.04  ------ Proving...
% 2.94/1.04  ------ Problem Properties 
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  clauses                                 11
% 2.94/1.04  conjectures                             2
% 2.94/1.04  EPR                                     1
% 2.94/1.04  Horn                                    9
% 2.94/1.04  unary                                   1
% 2.94/1.04  binary                                  6
% 2.94/1.04  lits                                    25
% 2.94/1.04  lits eq                                 6
% 2.94/1.04  fd_pure                                 0
% 2.94/1.04  fd_pseudo                               0
% 2.94/1.04  fd_cond                                 0
% 2.94/1.04  fd_pseudo_cond                          4
% 2.94/1.04  AC symbols                              0
% 2.94/1.04  
% 2.94/1.04  ------ Input Options Time Limit: Unbounded
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  ------ 
% 2.94/1.04  Current options:
% 2.94/1.04  ------ 
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  ------ Proving...
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  % SZS status Theorem for theBenchmark.p
% 2.94/1.04  
% 2.94/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.94/1.04  
% 2.94/1.04  fof(f2,axiom,(
% 2.94/1.04    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.94/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.04  
% 2.94/1.04  fof(f28,plain,(
% 2.94/1.04    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.94/1.04    inference(cnf_transformation,[],[f2])).
% 2.94/1.04  
% 2.94/1.04  fof(f3,axiom,(
% 2.94/1.04    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 2.94/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.04  
% 2.94/1.04  fof(f9,plain,(
% 2.94/1.04    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.94/1.04    inference(ennf_transformation,[],[f3])).
% 2.94/1.04  
% 2.94/1.04  fof(f29,plain,(
% 2.94/1.04    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.94/1.04    inference(cnf_transformation,[],[f9])).
% 2.94/1.04  
% 2.94/1.04  fof(f4,axiom,(
% 2.94/1.04    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.94/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.04  
% 2.94/1.04  fof(f15,plain,(
% 2.94/1.04    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.94/1.04    inference(nnf_transformation,[],[f4])).
% 2.94/1.04  
% 2.94/1.04  fof(f16,plain,(
% 2.94/1.04    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.94/1.04    inference(rectify,[],[f15])).
% 2.94/1.04  
% 2.94/1.04  fof(f19,plain,(
% 2.94/1.04    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.94/1.04    introduced(choice_axiom,[])).
% 2.94/1.04  
% 2.94/1.04  fof(f18,plain,(
% 2.94/1.04    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.94/1.04    introduced(choice_axiom,[])).
% 2.94/1.04  
% 2.94/1.04  fof(f17,plain,(
% 2.94/1.04    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.94/1.04    introduced(choice_axiom,[])).
% 2.94/1.04  
% 2.94/1.04  fof(f20,plain,(
% 2.94/1.04    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.94/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 2.94/1.04  
% 2.94/1.04  fof(f31,plain,(
% 2.94/1.04    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.94/1.04    inference(cnf_transformation,[],[f20])).
% 2.94/1.04  
% 2.94/1.04  fof(f39,plain,(
% 2.94/1.04    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.94/1.04    inference(equality_resolution,[],[f31])).
% 2.94/1.04  
% 2.94/1.04  fof(f5,axiom,(
% 2.94/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.94/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.04  
% 2.94/1.04  fof(f10,plain,(
% 2.94/1.04    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.94/1.04    inference(ennf_transformation,[],[f5])).
% 2.94/1.04  
% 2.94/1.04  fof(f21,plain,(
% 2.94/1.04    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.94/1.04    inference(nnf_transformation,[],[f10])).
% 2.94/1.04  
% 2.94/1.04  fof(f35,plain,(
% 2.94/1.04    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.94/1.04    inference(cnf_transformation,[],[f21])).
% 2.94/1.04  
% 2.94/1.04  fof(f6,conjecture,(
% 2.94/1.04    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.94/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.04  
% 2.94/1.04  fof(f7,negated_conjecture,(
% 2.94/1.04    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.94/1.04    inference(negated_conjecture,[],[f6])).
% 2.94/1.04  
% 2.94/1.04  fof(f11,plain,(
% 2.94/1.04    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 2.94/1.04    inference(ennf_transformation,[],[f7])).
% 2.94/1.04  
% 2.94/1.04  fof(f22,plain,(
% 2.94/1.04    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 2.94/1.04    inference(nnf_transformation,[],[f11])).
% 2.94/1.04  
% 2.94/1.04  fof(f23,plain,(
% 2.94/1.04    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.94/1.04    inference(flattening,[],[f22])).
% 2.94/1.04  
% 2.94/1.04  fof(f24,plain,(
% 2.94/1.04    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))) & (k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))) & v1_relat_1(sK5))),
% 2.94/1.04    introduced(choice_axiom,[])).
% 2.94/1.04  
% 2.94/1.04  fof(f25,plain,(
% 2.94/1.04    (k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))) & (k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))) & v1_relat_1(sK5)),
% 2.94/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f24])).
% 2.94/1.04  
% 2.94/1.04  fof(f36,plain,(
% 2.94/1.04    v1_relat_1(sK5)),
% 2.94/1.04    inference(cnf_transformation,[],[f25])).
% 2.94/1.04  
% 2.94/1.04  fof(f34,plain,(
% 2.94/1.04    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 2.94/1.04    inference(cnf_transformation,[],[f21])).
% 2.94/1.04  
% 2.94/1.04  fof(f30,plain,(
% 2.94/1.04    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.94/1.04    inference(cnf_transformation,[],[f20])).
% 2.94/1.04  
% 2.94/1.04  fof(f40,plain,(
% 2.94/1.04    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.94/1.04    inference(equality_resolution,[],[f30])).
% 2.94/1.04  
% 2.94/1.04  fof(f1,axiom,(
% 2.94/1.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.94/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.94/1.04  
% 2.94/1.04  fof(f8,plain,(
% 2.94/1.04    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.94/1.04    inference(ennf_transformation,[],[f1])).
% 2.94/1.04  
% 2.94/1.04  fof(f12,plain,(
% 2.94/1.04    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.94/1.04    inference(nnf_transformation,[],[f8])).
% 2.94/1.04  
% 2.94/1.04  fof(f13,plain,(
% 2.94/1.04    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.94/1.04    introduced(choice_axiom,[])).
% 2.94/1.04  
% 2.94/1.04  fof(f14,plain,(
% 2.94/1.04    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 2.94/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 2.94/1.04  
% 2.94/1.04  fof(f26,plain,(
% 2.94/1.04    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.94/1.04    inference(cnf_transformation,[],[f14])).
% 2.94/1.04  
% 2.94/1.04  fof(f38,plain,(
% 2.94/1.04    k1_xboole_0 = k11_relat_1(sK5,sK4) | ~r2_hidden(sK4,k1_relat_1(sK5))),
% 2.94/1.04    inference(cnf_transformation,[],[f25])).
% 2.94/1.04  
% 2.94/1.04  fof(f37,plain,(
% 2.94/1.04    k1_xboole_0 != k11_relat_1(sK5,sK4) | r2_hidden(sK4,k1_relat_1(sK5))),
% 2.94/1.04    inference(cnf_transformation,[],[f25])).
% 2.94/1.04  
% 2.94/1.04  cnf(c_2,plain,
% 2.94/1.04      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.94/1.04      inference(cnf_transformation,[],[f28]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_3,plain,
% 2.94/1.04      ( ~ r1_xboole_0(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.94/1.04      inference(cnf_transformation,[],[f29]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_184,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,X1) | k1_tarski(X0) != X2 | k1_xboole_0 != X1 ),
% 2.94/1.04      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_185,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.94/1.04      inference(unflattening,[status(thm)],[c_184]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_4912,plain,
% 2.94/1.04      ( ~ r2_hidden(sK3(sK5,sK4),k1_xboole_0) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_185]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_342,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.94/1.04      theory(equality) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_941,plain,
% 2.94/1.04      ( r2_hidden(X0,X1)
% 2.94/1.04      | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.94/1.04      | X1 != k11_relat_1(sK5,sK4)
% 2.94/1.04      | X0 != sK3(sK5,sK4) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_342]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_2136,plain,
% 2.94/1.04      ( r2_hidden(sK3(sK5,sK4),X0)
% 2.94/1.04      | ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.94/1.04      | X0 != k11_relat_1(sK5,sK4)
% 2.94/1.04      | sK3(sK5,sK4) != sK3(sK5,sK4) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_941]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_4366,plain,
% 2.94/1.04      ( ~ r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.94/1.04      | r2_hidden(sK3(sK5,sK4),k1_xboole_0)
% 2.94/1.04      | sK3(sK5,sK4) != sK3(sK5,sK4)
% 2.94/1.04      | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_2136]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_340,plain,( X0 = X0 ),theory(equality) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_2137,plain,
% 2.94/1.04      ( sK3(sK5,sK4) = sK3(sK5,sK4) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_340]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_6,plain,
% 2.94/1.04      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.94/1.04      inference(cnf_transformation,[],[f39]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_1278,plain,
% 2.94/1.04      ( ~ r2_hidden(k4_tarski(sK4,sK0(k11_relat_1(sK5,sK4),k1_xboole_0)),sK5)
% 2.94/1.04      | r2_hidden(sK4,k1_relat_1(sK5)) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_8,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.94/1.04      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.04      | ~ v1_relat_1(X1) ),
% 2.94/1.04      inference(cnf_transformation,[],[f35]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_12,negated_conjecture,
% 2.94/1.04      ( v1_relat_1(sK5) ),
% 2.94/1.04      inference(cnf_transformation,[],[f36]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_207,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.94/1.04      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.04      | sK5 != X1 ),
% 2.94/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_208,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
% 2.94/1.04      | r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.94/1.04      inference(unflattening,[status(thm)],[c_207]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_268,plain,
% 2.94/1.04      ( r2_hidden(k4_tarski(X1,X0),sK5)
% 2.94/1.04      | ~ r2_hidden(X0,k11_relat_1(sK5,X1)) ),
% 2.94/1.04      inference(prop_impl,[status(thm)],[c_208]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_269,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,k11_relat_1(sK5,X1))
% 2.94/1.04      | r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.94/1.04      inference(renaming,[status(thm)],[c_268]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_826,plain,
% 2.94/1.04      ( r2_hidden(k4_tarski(sK4,sK0(k11_relat_1(sK5,sK4),k1_xboole_0)),sK5)
% 2.94/1.04      | ~ r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k11_relat_1(sK5,sK4)) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_269]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_9,plain,
% 2.94/1.04      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.94/1.04      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.04      | ~ v1_relat_1(X1) ),
% 2.94/1.04      inference(cnf_transformation,[],[f34]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_195,plain,
% 2.94/1.04      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 2.94/1.04      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 2.94/1.04      | sK5 != X1 ),
% 2.94/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_196,plain,
% 2.94/1.04      ( r2_hidden(X0,k11_relat_1(sK5,X1))
% 2.94/1.04      | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.94/1.04      inference(unflattening,[status(thm)],[c_195]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_270,plain,
% 2.94/1.04      ( ~ r2_hidden(k4_tarski(X1,X0),sK5)
% 2.94/1.04      | r2_hidden(X0,k11_relat_1(sK5,X1)) ),
% 2.94/1.04      inference(prop_impl,[status(thm)],[c_196]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_271,plain,
% 2.94/1.04      ( r2_hidden(X0,k11_relat_1(sK5,X1))
% 2.94/1.04      | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 2.94/1.04      inference(renaming,[status(thm)],[c_270]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_807,plain,
% 2.94/1.04      ( r2_hidden(sK3(sK5,sK4),k11_relat_1(sK5,sK4))
% 2.94/1.04      | ~ r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_271]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_7,plain,
% 2.94/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.94/1.04      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.94/1.04      inference(cnf_transformation,[],[f40]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_796,plain,
% 2.94/1.04      ( r2_hidden(k4_tarski(sK4,sK3(sK5,sK4)),sK5)
% 2.94/1.04      | ~ r2_hidden(sK4,k1_relat_1(sK5)) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_767,plain,
% 2.94/1.04      ( ~ r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_185]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_1,plain,
% 2.94/1.04      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 2.94/1.04      inference(cnf_transformation,[],[f26]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_759,plain,
% 2.94/1.04      ( r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k11_relat_1(sK5,sK4))
% 2.94/1.04      | r2_hidden(sK0(k11_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
% 2.94/1.04      | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
% 2.94/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_10,negated_conjecture,
% 2.94/1.04      ( ~ r2_hidden(sK4,k1_relat_1(sK5))
% 2.94/1.04      | k1_xboole_0 = k11_relat_1(sK5,sK4) ),
% 2.94/1.04      inference(cnf_transformation,[],[f38]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(c_11,negated_conjecture,
% 2.94/1.04      ( r2_hidden(sK4,k1_relat_1(sK5))
% 2.94/1.04      | k1_xboole_0 != k11_relat_1(sK5,sK4) ),
% 2.94/1.04      inference(cnf_transformation,[],[f37]) ).
% 2.94/1.04  
% 2.94/1.04  cnf(contradiction,plain,
% 2.94/1.04      ( $false ),
% 2.94/1.04      inference(minisat,
% 2.94/1.04                [status(thm)],
% 2.94/1.04                [c_4912,c_4366,c_2137,c_1278,c_826,c_807,c_796,c_767,
% 2.94/1.04                 c_759,c_10,c_11]) ).
% 2.94/1.04  
% 2.94/1.04  
% 2.94/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.94/1.04  
% 2.94/1.04  ------                               Statistics
% 2.94/1.04  
% 2.94/1.04  ------ Selected
% 2.94/1.04  
% 2.94/1.04  total_time:                             0.119
% 2.94/1.04  
%------------------------------------------------------------------------------

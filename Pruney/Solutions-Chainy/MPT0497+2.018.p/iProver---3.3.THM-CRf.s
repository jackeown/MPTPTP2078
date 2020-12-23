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
% DateTime   : Thu Dec  3 11:44:49 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 181 expanded)
%              Number of clauses        :   63 (  73 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  346 ( 658 expanded)
%              Number of equality atoms :   97 ( 142 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27,f26,f25])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK5),sK4)
        | k1_xboole_0 != k7_relat_1(sK5,sK4) )
      & ( r1_xboole_0(k1_relat_1(sK5),sK4)
        | k1_xboole_0 = k7_relat_1(sK5,sK4) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK5),sK4)
      | k1_xboole_0 != k7_relat_1(sK5,sK4) )
    & ( r1_xboole_0(k1_relat_1(sK5),sK4)
      | k1_xboole_0 = k7_relat_1(sK5,sK4) )
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f33])).

fof(f54,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK4)
    | k1_xboole_0 = k7_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK5),sK4)
    | k1_xboole_0 != k7_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5851,plain,
    ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),X0)
    | ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK4)
    | ~ r1_xboole_0(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_8102,plain,
    ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(sK5))
    | ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK4)
    | ~ r1_xboole_0(k1_relat_1(sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_5851])).

cnf(c_262,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2141,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(sK5,sK4)))
    | X0 != sK0(k1_relat_1(sK5),sK4)
    | X1 != k1_relat_1(k7_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_6475,plain,
    ( r2_hidden(sK0(k1_relat_1(sK5),sK4),X0)
    | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(sK5,sK4)))
    | X0 != k1_relat_1(k7_relat_1(sK5,sK4))
    | sK0(k1_relat_1(sK5),sK4) != sK0(k1_relat_1(sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_6478,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(sK5,sK4)))
    | r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_xboole_0)
    | sK0(k1_relat_1(sK5),sK4) != sK0(k1_relat_1(sK5),sK4)
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_6475])).

cnf(c_260,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1912,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_4896,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK4)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_4897,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK4)) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK4))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4896])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3625,plain,
    ( r1_xboole_0(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_259,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3339,plain,
    ( sK0(k1_relat_1(sK5),sK4) = sK0(k1_relat_1(sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_906,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK5,X1)))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2349,plain,
    ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(k7_relat_1(sK5,sK4)))
    | r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK4)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_901,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK5,X1)))
    | r2_hidden(X0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2350,plain,
    ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(k7_relat_1(sK5,sK4)))
    | r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_1913,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1163,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(X0))
    | r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(X0,sK4)))
    | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1603,plain,
    ( r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(sK5,sK4)))
    | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(sK5))
    | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1489,plain,
    ( r1_xboole_0(X0,sK4)
    | ~ r1_xboole_0(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1491,plain,
    ( ~ r1_xboole_0(sK4,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_263,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1477,plain,
    ( k7_relat_1(sK5,sK4) != X0
    | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_1479,plain,
    ( k7_relat_1(sK5,sK4) != k1_xboole_0
    | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1045,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK4)) != X0
    | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_1476,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK4)) != k1_relat_1(X0)
    | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1478,plain,
    ( k1_relat_1(k7_relat_1(sK5,sK4)) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1464,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK2(k7_relat_1(sK5,sK4),k1_xboole_0)),k7_relat_1(sK5,sK4))
    | r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(k7_relat_1(sK5,sK4))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1166,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),X0)
    | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
    | ~ r1_xboole_0(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1171,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
    | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1116,plain,
    ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),X0)
    | ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1121,plain,
    ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK5),sK4)
    | k1_xboole_0 = k7_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_720,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK4)
    | r1_xboole_0(k1_relat_1(sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_737,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_991,plain,
    ( k7_relat_1(sK5,sK4) = k1_xboole_0
    | r1_xboole_0(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_737])).

cnf(c_1101,plain,
    ( k7_relat_1(sK5,sK4) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_737])).

cnf(c_1102,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK4)
    | k7_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1101])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1037,plain,
    ( r2_hidden(k4_tarski(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK2(k7_relat_1(sK5,sK4),k1_xboole_0)),k7_relat_1(sK5,sK4))
    | r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_873,plain,
    ( v1_relat_1(k7_relat_1(sK5,X0))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1000,plain,
    ( v1_relat_1(k7_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_924,plain,
    ( ~ v1_relat_1(k7_relat_1(sK5,sK4))
    | k1_relat_1(k7_relat_1(sK5,sK4)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_894,plain,
    ( r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(sK5))
    | r1_xboole_0(k1_relat_1(sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_891,plain,
    ( r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
    | r1_xboole_0(k1_relat_1(sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_276,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_54,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK5),sK4)
    | k1_xboole_0 != k7_relat_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8102,c_6478,c_4897,c_3625,c_3339,c_2349,c_2350,c_1913,c_1603,c_1491,c_1479,c_1478,c_1464,c_1171,c_1121,c_1102,c_1037,c_1000,c_924,c_894,c_891,c_276,c_54,c_12,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:36:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.96/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.02  
% 3.96/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/1.02  
% 3.96/1.02  ------  iProver source info
% 3.96/1.02  
% 3.96/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.96/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/1.02  git: non_committed_changes: false
% 3.96/1.02  git: last_make_outside_of_git: false
% 3.96/1.02  
% 3.96/1.02  ------ 
% 3.96/1.02  
% 3.96/1.02  ------ Input Options
% 3.96/1.02  
% 3.96/1.02  --out_options                           all
% 3.96/1.02  --tptp_safe_out                         true
% 3.96/1.02  --problem_path                          ""
% 3.96/1.02  --include_path                          ""
% 3.96/1.02  --clausifier                            res/vclausify_rel
% 3.96/1.02  --clausifier_options                    --mode clausify
% 3.96/1.02  --stdin                                 false
% 3.96/1.02  --stats_out                             all
% 3.96/1.02  
% 3.96/1.02  ------ General Options
% 3.96/1.02  
% 3.96/1.02  --fof                                   false
% 3.96/1.02  --time_out_real                         305.
% 3.96/1.02  --time_out_virtual                      -1.
% 3.96/1.02  --symbol_type_check                     false
% 3.96/1.02  --clausify_out                          false
% 3.96/1.02  --sig_cnt_out                           false
% 3.96/1.02  --trig_cnt_out                          false
% 3.96/1.02  --trig_cnt_out_tolerance                1.
% 3.96/1.02  --trig_cnt_out_sk_spl                   false
% 3.96/1.02  --abstr_cl_out                          false
% 3.96/1.02  
% 3.96/1.02  ------ Global Options
% 3.96/1.02  
% 3.96/1.02  --schedule                              default
% 3.96/1.02  --add_important_lit                     false
% 3.96/1.02  --prop_solver_per_cl                    1000
% 3.96/1.02  --min_unsat_core                        false
% 3.96/1.02  --soft_assumptions                      false
% 3.96/1.02  --soft_lemma_size                       3
% 3.96/1.02  --prop_impl_unit_size                   0
% 3.96/1.02  --prop_impl_unit                        []
% 3.96/1.02  --share_sel_clauses                     true
% 3.96/1.02  --reset_solvers                         false
% 3.96/1.02  --bc_imp_inh                            [conj_cone]
% 3.96/1.02  --conj_cone_tolerance                   3.
% 3.96/1.02  --extra_neg_conj                        none
% 3.96/1.02  --large_theory_mode                     true
% 3.96/1.02  --prolific_symb_bound                   200
% 3.96/1.02  --lt_threshold                          2000
% 3.96/1.02  --clause_weak_htbl                      true
% 3.96/1.02  --gc_record_bc_elim                     false
% 3.96/1.02  
% 3.96/1.02  ------ Preprocessing Options
% 3.96/1.02  
% 3.96/1.02  --preprocessing_flag                    true
% 3.96/1.02  --time_out_prep_mult                    0.1
% 3.96/1.02  --splitting_mode                        input
% 3.96/1.02  --splitting_grd                         true
% 3.96/1.02  --splitting_cvd                         false
% 3.96/1.02  --splitting_cvd_svl                     false
% 3.96/1.02  --splitting_nvd                         32
% 3.96/1.02  --sub_typing                            true
% 3.96/1.02  --prep_gs_sim                           true
% 3.96/1.02  --prep_unflatten                        true
% 3.96/1.02  --prep_res_sim                          true
% 3.96/1.02  --prep_upred                            true
% 3.96/1.02  --prep_sem_filter                       exhaustive
% 3.96/1.02  --prep_sem_filter_out                   false
% 3.96/1.02  --pred_elim                             true
% 3.96/1.02  --res_sim_input                         true
% 3.96/1.02  --eq_ax_congr_red                       true
% 3.96/1.02  --pure_diseq_elim                       true
% 3.96/1.02  --brand_transform                       false
% 3.96/1.02  --non_eq_to_eq                          false
% 3.96/1.02  --prep_def_merge                        true
% 3.96/1.02  --prep_def_merge_prop_impl              false
% 3.96/1.02  --prep_def_merge_mbd                    true
% 3.96/1.02  --prep_def_merge_tr_red                 false
% 3.96/1.02  --prep_def_merge_tr_cl                  false
% 3.96/1.02  --smt_preprocessing                     true
% 3.96/1.02  --smt_ac_axioms                         fast
% 3.96/1.02  --preprocessed_out                      false
% 3.96/1.02  --preprocessed_stats                    false
% 3.96/1.02  
% 3.96/1.02  ------ Abstraction refinement Options
% 3.96/1.02  
% 3.96/1.02  --abstr_ref                             []
% 3.96/1.02  --abstr_ref_prep                        false
% 3.96/1.02  --abstr_ref_until_sat                   false
% 3.96/1.02  --abstr_ref_sig_restrict                funpre
% 3.96/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/1.02  --abstr_ref_under                       []
% 3.96/1.02  
% 3.96/1.02  ------ SAT Options
% 3.96/1.02  
% 3.96/1.02  --sat_mode                              false
% 3.96/1.02  --sat_fm_restart_options                ""
% 3.96/1.02  --sat_gr_def                            false
% 3.96/1.02  --sat_epr_types                         true
% 3.96/1.02  --sat_non_cyclic_types                  false
% 3.96/1.02  --sat_finite_models                     false
% 3.96/1.02  --sat_fm_lemmas                         false
% 3.96/1.02  --sat_fm_prep                           false
% 3.96/1.02  --sat_fm_uc_incr                        true
% 3.96/1.02  --sat_out_model                         small
% 3.96/1.02  --sat_out_clauses                       false
% 3.96/1.02  
% 3.96/1.02  ------ QBF Options
% 3.96/1.02  
% 3.96/1.02  --qbf_mode                              false
% 3.96/1.02  --qbf_elim_univ                         false
% 3.96/1.02  --qbf_dom_inst                          none
% 3.96/1.02  --qbf_dom_pre_inst                      false
% 3.96/1.02  --qbf_sk_in                             false
% 3.96/1.02  --qbf_pred_elim                         true
% 3.96/1.02  --qbf_split                             512
% 3.96/1.02  
% 3.96/1.02  ------ BMC1 Options
% 3.96/1.02  
% 3.96/1.02  --bmc1_incremental                      false
% 3.96/1.02  --bmc1_axioms                           reachable_all
% 3.96/1.02  --bmc1_min_bound                        0
% 3.96/1.02  --bmc1_max_bound                        -1
% 3.96/1.02  --bmc1_max_bound_default                -1
% 3.96/1.02  --bmc1_symbol_reachability              true
% 3.96/1.02  --bmc1_property_lemmas                  false
% 3.96/1.02  --bmc1_k_induction                      false
% 3.96/1.02  --bmc1_non_equiv_states                 false
% 3.96/1.02  --bmc1_deadlock                         false
% 3.96/1.02  --bmc1_ucm                              false
% 3.96/1.02  --bmc1_add_unsat_core                   none
% 3.96/1.02  --bmc1_unsat_core_children              false
% 3.96/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/1.02  --bmc1_out_stat                         full
% 3.96/1.02  --bmc1_ground_init                      false
% 3.96/1.02  --bmc1_pre_inst_next_state              false
% 3.96/1.02  --bmc1_pre_inst_state                   false
% 3.96/1.02  --bmc1_pre_inst_reach_state             false
% 3.96/1.02  --bmc1_out_unsat_core                   false
% 3.96/1.02  --bmc1_aig_witness_out                  false
% 3.96/1.02  --bmc1_verbose                          false
% 3.96/1.02  --bmc1_dump_clauses_tptp                false
% 3.96/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.96/1.02  --bmc1_dump_file                        -
% 3.96/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.96/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.96/1.02  --bmc1_ucm_extend_mode                  1
% 3.96/1.02  --bmc1_ucm_init_mode                    2
% 3.96/1.02  --bmc1_ucm_cone_mode                    none
% 3.96/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.96/1.02  --bmc1_ucm_relax_model                  4
% 3.96/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.96/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/1.02  --bmc1_ucm_layered_model                none
% 3.96/1.02  --bmc1_ucm_max_lemma_size               10
% 3.96/1.02  
% 3.96/1.02  ------ AIG Options
% 3.96/1.02  
% 3.96/1.02  --aig_mode                              false
% 3.96/1.02  
% 3.96/1.02  ------ Instantiation Options
% 3.96/1.02  
% 3.96/1.02  --instantiation_flag                    true
% 3.96/1.02  --inst_sos_flag                         false
% 3.96/1.02  --inst_sos_phase                        true
% 3.96/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/1.02  --inst_lit_sel_side                     num_symb
% 3.96/1.02  --inst_solver_per_active                1400
% 3.96/1.02  --inst_solver_calls_frac                1.
% 3.96/1.02  --inst_passive_queue_type               priority_queues
% 3.96/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/1.02  --inst_passive_queues_freq              [25;2]
% 3.96/1.02  --inst_dismatching                      true
% 3.96/1.02  --inst_eager_unprocessed_to_passive     true
% 3.96/1.02  --inst_prop_sim_given                   true
% 3.96/1.02  --inst_prop_sim_new                     false
% 3.96/1.02  --inst_subs_new                         false
% 3.96/1.02  --inst_eq_res_simp                      false
% 3.96/1.02  --inst_subs_given                       false
% 3.96/1.02  --inst_orphan_elimination               true
% 3.96/1.02  --inst_learning_loop_flag               true
% 3.96/1.02  --inst_learning_start                   3000
% 3.96/1.02  --inst_learning_factor                  2
% 3.96/1.02  --inst_start_prop_sim_after_learn       3
% 3.96/1.02  --inst_sel_renew                        solver
% 3.96/1.02  --inst_lit_activity_flag                true
% 3.96/1.02  --inst_restr_to_given                   false
% 3.96/1.02  --inst_activity_threshold               500
% 3.96/1.02  --inst_out_proof                        true
% 3.96/1.02  
% 3.96/1.02  ------ Resolution Options
% 3.96/1.02  
% 3.96/1.02  --resolution_flag                       true
% 3.96/1.02  --res_lit_sel                           adaptive
% 3.96/1.02  --res_lit_sel_side                      none
% 3.96/1.02  --res_ordering                          kbo
% 3.96/1.02  --res_to_prop_solver                    active
% 3.96/1.02  --res_prop_simpl_new                    false
% 3.96/1.02  --res_prop_simpl_given                  true
% 3.96/1.02  --res_passive_queue_type                priority_queues
% 3.96/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/1.02  --res_passive_queues_freq               [15;5]
% 3.96/1.02  --res_forward_subs                      full
% 3.96/1.02  --res_backward_subs                     full
% 3.96/1.02  --res_forward_subs_resolution           true
% 3.96/1.02  --res_backward_subs_resolution          true
% 3.96/1.02  --res_orphan_elimination                true
% 3.96/1.02  --res_time_limit                        2.
% 3.96/1.02  --res_out_proof                         true
% 3.96/1.02  
% 3.96/1.02  ------ Superposition Options
% 3.96/1.02  
% 3.96/1.02  --superposition_flag                    true
% 3.96/1.02  --sup_passive_queue_type                priority_queues
% 3.96/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.96/1.02  --demod_completeness_check              fast
% 3.96/1.02  --demod_use_ground                      true
% 3.96/1.02  --sup_to_prop_solver                    passive
% 3.96/1.02  --sup_prop_simpl_new                    true
% 3.96/1.02  --sup_prop_simpl_given                  true
% 3.96/1.02  --sup_fun_splitting                     false
% 3.96/1.02  --sup_smt_interval                      50000
% 3.96/1.02  
% 3.96/1.02  ------ Superposition Simplification Setup
% 3.96/1.02  
% 3.96/1.02  --sup_indices_passive                   []
% 3.96/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.02  --sup_full_bw                           [BwDemod]
% 3.96/1.02  --sup_immed_triv                        [TrivRules]
% 3.96/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.02  --sup_immed_bw_main                     []
% 3.96/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.02  
% 3.96/1.02  ------ Combination Options
% 3.96/1.02  
% 3.96/1.02  --comb_res_mult                         3
% 3.96/1.02  --comb_sup_mult                         2
% 3.96/1.02  --comb_inst_mult                        10
% 3.96/1.02  
% 3.96/1.02  ------ Debug Options
% 3.96/1.02  
% 3.96/1.02  --dbg_backtrace                         false
% 3.96/1.02  --dbg_dump_prop_clauses                 false
% 3.96/1.02  --dbg_dump_prop_clauses_file            -
% 3.96/1.02  --dbg_out_stat                          false
% 3.96/1.02  ------ Parsing...
% 3.96/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/1.02  
% 3.96/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.96/1.02  
% 3.96/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/1.02  
% 3.96/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.02  ------ Proving...
% 3.96/1.02  ------ Problem Properties 
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  clauses                                 21
% 3.96/1.02  conjectures                             3
% 3.96/1.02  EPR                                     4
% 3.96/1.02  Horn                                    17
% 3.96/1.02  unary                                   4
% 3.96/1.02  binary                                  9
% 3.96/1.02  lits                                    47
% 3.96/1.02  lits eq                                 10
% 3.96/1.02  fd_pure                                 0
% 3.96/1.02  fd_pseudo                               0
% 3.96/1.02  fd_cond                                 2
% 3.96/1.02  fd_pseudo_cond                          2
% 3.96/1.02  AC symbols                              0
% 3.96/1.02  
% 3.96/1.02  ------ Schedule dynamic 5 is on 
% 3.96/1.02  
% 3.96/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  ------ 
% 3.96/1.02  Current options:
% 3.96/1.02  ------ 
% 3.96/1.02  
% 3.96/1.02  ------ Input Options
% 3.96/1.02  
% 3.96/1.02  --out_options                           all
% 3.96/1.02  --tptp_safe_out                         true
% 3.96/1.02  --problem_path                          ""
% 3.96/1.02  --include_path                          ""
% 3.96/1.02  --clausifier                            res/vclausify_rel
% 3.96/1.02  --clausifier_options                    --mode clausify
% 3.96/1.02  --stdin                                 false
% 3.96/1.02  --stats_out                             all
% 3.96/1.02  
% 3.96/1.02  ------ General Options
% 3.96/1.02  
% 3.96/1.02  --fof                                   false
% 3.96/1.02  --time_out_real                         305.
% 3.96/1.02  --time_out_virtual                      -1.
% 3.96/1.02  --symbol_type_check                     false
% 3.96/1.02  --clausify_out                          false
% 3.96/1.02  --sig_cnt_out                           false
% 3.96/1.02  --trig_cnt_out                          false
% 3.96/1.02  --trig_cnt_out_tolerance                1.
% 3.96/1.02  --trig_cnt_out_sk_spl                   false
% 3.96/1.02  --abstr_cl_out                          false
% 3.96/1.02  
% 3.96/1.02  ------ Global Options
% 3.96/1.02  
% 3.96/1.02  --schedule                              default
% 3.96/1.02  --add_important_lit                     false
% 3.96/1.02  --prop_solver_per_cl                    1000
% 3.96/1.02  --min_unsat_core                        false
% 3.96/1.02  --soft_assumptions                      false
% 3.96/1.02  --soft_lemma_size                       3
% 3.96/1.02  --prop_impl_unit_size                   0
% 3.96/1.02  --prop_impl_unit                        []
% 3.96/1.02  --share_sel_clauses                     true
% 3.96/1.02  --reset_solvers                         false
% 3.96/1.02  --bc_imp_inh                            [conj_cone]
% 3.96/1.02  --conj_cone_tolerance                   3.
% 3.96/1.02  --extra_neg_conj                        none
% 3.96/1.02  --large_theory_mode                     true
% 3.96/1.02  --prolific_symb_bound                   200
% 3.96/1.02  --lt_threshold                          2000
% 3.96/1.02  --clause_weak_htbl                      true
% 3.96/1.02  --gc_record_bc_elim                     false
% 3.96/1.02  
% 3.96/1.02  ------ Preprocessing Options
% 3.96/1.02  
% 3.96/1.02  --preprocessing_flag                    true
% 3.96/1.02  --time_out_prep_mult                    0.1
% 3.96/1.02  --splitting_mode                        input
% 3.96/1.02  --splitting_grd                         true
% 3.96/1.02  --splitting_cvd                         false
% 3.96/1.02  --splitting_cvd_svl                     false
% 3.96/1.02  --splitting_nvd                         32
% 3.96/1.02  --sub_typing                            true
% 3.96/1.02  --prep_gs_sim                           true
% 3.96/1.02  --prep_unflatten                        true
% 3.96/1.02  --prep_res_sim                          true
% 3.96/1.02  --prep_upred                            true
% 3.96/1.02  --prep_sem_filter                       exhaustive
% 3.96/1.02  --prep_sem_filter_out                   false
% 3.96/1.02  --pred_elim                             true
% 3.96/1.02  --res_sim_input                         true
% 3.96/1.02  --eq_ax_congr_red                       true
% 3.96/1.02  --pure_diseq_elim                       true
% 3.96/1.02  --brand_transform                       false
% 3.96/1.02  --non_eq_to_eq                          false
% 3.96/1.02  --prep_def_merge                        true
% 3.96/1.02  --prep_def_merge_prop_impl              false
% 3.96/1.02  --prep_def_merge_mbd                    true
% 3.96/1.02  --prep_def_merge_tr_red                 false
% 3.96/1.02  --prep_def_merge_tr_cl                  false
% 3.96/1.02  --smt_preprocessing                     true
% 3.96/1.02  --smt_ac_axioms                         fast
% 3.96/1.02  --preprocessed_out                      false
% 3.96/1.02  --preprocessed_stats                    false
% 3.96/1.02  
% 3.96/1.02  ------ Abstraction refinement Options
% 3.96/1.02  
% 3.96/1.02  --abstr_ref                             []
% 3.96/1.02  --abstr_ref_prep                        false
% 3.96/1.02  --abstr_ref_until_sat                   false
% 3.96/1.02  --abstr_ref_sig_restrict                funpre
% 3.96/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/1.02  --abstr_ref_under                       []
% 3.96/1.02  
% 3.96/1.02  ------ SAT Options
% 3.96/1.02  
% 3.96/1.02  --sat_mode                              false
% 3.96/1.02  --sat_fm_restart_options                ""
% 3.96/1.02  --sat_gr_def                            false
% 3.96/1.02  --sat_epr_types                         true
% 3.96/1.02  --sat_non_cyclic_types                  false
% 3.96/1.02  --sat_finite_models                     false
% 3.96/1.02  --sat_fm_lemmas                         false
% 3.96/1.02  --sat_fm_prep                           false
% 3.96/1.02  --sat_fm_uc_incr                        true
% 3.96/1.02  --sat_out_model                         small
% 3.96/1.02  --sat_out_clauses                       false
% 3.96/1.02  
% 3.96/1.02  ------ QBF Options
% 3.96/1.02  
% 3.96/1.02  --qbf_mode                              false
% 3.96/1.02  --qbf_elim_univ                         false
% 3.96/1.02  --qbf_dom_inst                          none
% 3.96/1.02  --qbf_dom_pre_inst                      false
% 3.96/1.02  --qbf_sk_in                             false
% 3.96/1.02  --qbf_pred_elim                         true
% 3.96/1.02  --qbf_split                             512
% 3.96/1.02  
% 3.96/1.02  ------ BMC1 Options
% 3.96/1.02  
% 3.96/1.02  --bmc1_incremental                      false
% 3.96/1.02  --bmc1_axioms                           reachable_all
% 3.96/1.02  --bmc1_min_bound                        0
% 3.96/1.02  --bmc1_max_bound                        -1
% 3.96/1.02  --bmc1_max_bound_default                -1
% 3.96/1.02  --bmc1_symbol_reachability              true
% 3.96/1.02  --bmc1_property_lemmas                  false
% 3.96/1.02  --bmc1_k_induction                      false
% 3.96/1.02  --bmc1_non_equiv_states                 false
% 3.96/1.02  --bmc1_deadlock                         false
% 3.96/1.02  --bmc1_ucm                              false
% 3.96/1.02  --bmc1_add_unsat_core                   none
% 3.96/1.02  --bmc1_unsat_core_children              false
% 3.96/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/1.02  --bmc1_out_stat                         full
% 3.96/1.02  --bmc1_ground_init                      false
% 3.96/1.02  --bmc1_pre_inst_next_state              false
% 3.96/1.02  --bmc1_pre_inst_state                   false
% 3.96/1.02  --bmc1_pre_inst_reach_state             false
% 3.96/1.02  --bmc1_out_unsat_core                   false
% 3.96/1.02  --bmc1_aig_witness_out                  false
% 3.96/1.02  --bmc1_verbose                          false
% 3.96/1.02  --bmc1_dump_clauses_tptp                false
% 3.96/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.96/1.02  --bmc1_dump_file                        -
% 3.96/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.96/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.96/1.02  --bmc1_ucm_extend_mode                  1
% 3.96/1.02  --bmc1_ucm_init_mode                    2
% 3.96/1.02  --bmc1_ucm_cone_mode                    none
% 3.96/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.96/1.02  --bmc1_ucm_relax_model                  4
% 3.96/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.96/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/1.02  --bmc1_ucm_layered_model                none
% 3.96/1.02  --bmc1_ucm_max_lemma_size               10
% 3.96/1.02  
% 3.96/1.02  ------ AIG Options
% 3.96/1.02  
% 3.96/1.02  --aig_mode                              false
% 3.96/1.02  
% 3.96/1.02  ------ Instantiation Options
% 3.96/1.02  
% 3.96/1.02  --instantiation_flag                    true
% 3.96/1.02  --inst_sos_flag                         false
% 3.96/1.02  --inst_sos_phase                        true
% 3.96/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/1.02  --inst_lit_sel_side                     none
% 3.96/1.02  --inst_solver_per_active                1400
% 3.96/1.02  --inst_solver_calls_frac                1.
% 3.96/1.02  --inst_passive_queue_type               priority_queues
% 3.96/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/1.02  --inst_passive_queues_freq              [25;2]
% 3.96/1.02  --inst_dismatching                      true
% 3.96/1.02  --inst_eager_unprocessed_to_passive     true
% 3.96/1.02  --inst_prop_sim_given                   true
% 3.96/1.02  --inst_prop_sim_new                     false
% 3.96/1.02  --inst_subs_new                         false
% 3.96/1.02  --inst_eq_res_simp                      false
% 3.96/1.02  --inst_subs_given                       false
% 3.96/1.02  --inst_orphan_elimination               true
% 3.96/1.02  --inst_learning_loop_flag               true
% 3.96/1.02  --inst_learning_start                   3000
% 3.96/1.02  --inst_learning_factor                  2
% 3.96/1.02  --inst_start_prop_sim_after_learn       3
% 3.96/1.02  --inst_sel_renew                        solver
% 3.96/1.02  --inst_lit_activity_flag                true
% 3.96/1.02  --inst_restr_to_given                   false
% 3.96/1.02  --inst_activity_threshold               500
% 3.96/1.02  --inst_out_proof                        true
% 3.96/1.02  
% 3.96/1.02  ------ Resolution Options
% 3.96/1.02  
% 3.96/1.02  --resolution_flag                       false
% 3.96/1.02  --res_lit_sel                           adaptive
% 3.96/1.02  --res_lit_sel_side                      none
% 3.96/1.02  --res_ordering                          kbo
% 3.96/1.02  --res_to_prop_solver                    active
% 3.96/1.02  --res_prop_simpl_new                    false
% 3.96/1.02  --res_prop_simpl_given                  true
% 3.96/1.02  --res_passive_queue_type                priority_queues
% 3.96/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/1.02  --res_passive_queues_freq               [15;5]
% 3.96/1.02  --res_forward_subs                      full
% 3.96/1.02  --res_backward_subs                     full
% 3.96/1.02  --res_forward_subs_resolution           true
% 3.96/1.02  --res_backward_subs_resolution          true
% 3.96/1.02  --res_orphan_elimination                true
% 3.96/1.02  --res_time_limit                        2.
% 3.96/1.02  --res_out_proof                         true
% 3.96/1.02  
% 3.96/1.02  ------ Superposition Options
% 3.96/1.02  
% 3.96/1.02  --superposition_flag                    true
% 3.96/1.02  --sup_passive_queue_type                priority_queues
% 3.96/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.96/1.02  --demod_completeness_check              fast
% 3.96/1.02  --demod_use_ground                      true
% 3.96/1.02  --sup_to_prop_solver                    passive
% 3.96/1.02  --sup_prop_simpl_new                    true
% 3.96/1.02  --sup_prop_simpl_given                  true
% 3.96/1.02  --sup_fun_splitting                     false
% 3.96/1.02  --sup_smt_interval                      50000
% 3.96/1.02  
% 3.96/1.02  ------ Superposition Simplification Setup
% 3.96/1.02  
% 3.96/1.02  --sup_indices_passive                   []
% 3.96/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.02  --sup_full_bw                           [BwDemod]
% 3.96/1.02  --sup_immed_triv                        [TrivRules]
% 3.96/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.02  --sup_immed_bw_main                     []
% 3.96/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.02  
% 3.96/1.02  ------ Combination Options
% 3.96/1.02  
% 3.96/1.02  --comb_res_mult                         3
% 3.96/1.02  --comb_sup_mult                         2
% 3.96/1.02  --comb_inst_mult                        10
% 3.96/1.02  
% 3.96/1.02  ------ Debug Options
% 3.96/1.02  
% 3.96/1.02  --dbg_backtrace                         false
% 3.96/1.02  --dbg_dump_prop_clauses                 false
% 3.96/1.02  --dbg_dump_prop_clauses_file            -
% 3.96/1.02  --dbg_out_stat                          false
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  ------ Proving...
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  % SZS status Theorem for theBenchmark.p
% 3.96/1.02  
% 3.96/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/1.02  
% 3.96/1.02  fof(f2,axiom,(
% 3.96/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f12,plain,(
% 3.96/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.96/1.02    inference(rectify,[],[f2])).
% 3.96/1.02  
% 3.96/1.02  fof(f14,plain,(
% 3.96/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.96/1.02    inference(ennf_transformation,[],[f12])).
% 3.96/1.02  
% 3.96/1.02  fof(f21,plain,(
% 3.96/1.02    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.96/1.02    introduced(choice_axiom,[])).
% 3.96/1.02  
% 3.96/1.02  fof(f22,plain,(
% 3.96/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).
% 3.96/1.02  
% 3.96/1.02  fof(f38,plain,(
% 3.96/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f22])).
% 3.96/1.02  
% 3.96/1.02  fof(f3,axiom,(
% 3.96/1.02    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f39,plain,(
% 3.96/1.02    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f3])).
% 3.96/1.02  
% 3.96/1.02  fof(f9,axiom,(
% 3.96/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f19,plain,(
% 3.96/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 3.96/1.02    inference(ennf_transformation,[],[f9])).
% 3.96/1.02  
% 3.96/1.02  fof(f29,plain,(
% 3.96/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.96/1.02    inference(nnf_transformation,[],[f19])).
% 3.96/1.02  
% 3.96/1.02  fof(f30,plain,(
% 3.96/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.96/1.02    inference(flattening,[],[f29])).
% 3.96/1.02  
% 3.96/1.02  fof(f50,plain,(
% 3.96/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f30])).
% 3.96/1.02  
% 3.96/1.02  fof(f51,plain,(
% 3.96/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f30])).
% 3.96/1.02  
% 3.96/1.02  fof(f52,plain,(
% 3.96/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f30])).
% 3.96/1.02  
% 3.96/1.02  fof(f1,axiom,(
% 3.96/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f13,plain,(
% 3.96/1.02    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.96/1.02    inference(ennf_transformation,[],[f1])).
% 3.96/1.02  
% 3.96/1.02  fof(f35,plain,(
% 3.96/1.02    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f13])).
% 3.96/1.02  
% 3.96/1.02  fof(f5,axiom,(
% 3.96/1.02    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f23,plain,(
% 3.96/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.96/1.02    inference(nnf_transformation,[],[f5])).
% 3.96/1.02  
% 3.96/1.02  fof(f24,plain,(
% 3.96/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.96/1.02    inference(rectify,[],[f23])).
% 3.96/1.02  
% 3.96/1.02  fof(f27,plain,(
% 3.96/1.02    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 3.96/1.02    introduced(choice_axiom,[])).
% 3.96/1.02  
% 3.96/1.02  fof(f26,plain,(
% 3.96/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 3.96/1.02    introduced(choice_axiom,[])).
% 3.96/1.02  
% 3.96/1.02  fof(f25,plain,(
% 3.96/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.96/1.02    introduced(choice_axiom,[])).
% 3.96/1.02  
% 3.96/1.02  fof(f28,plain,(
% 3.96/1.02    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27,f26,f25])).
% 3.96/1.02  
% 3.96/1.02  fof(f42,plain,(
% 3.96/1.02    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 3.96/1.02    inference(cnf_transformation,[],[f28])).
% 3.96/1.02  
% 3.96/1.02  fof(f56,plain,(
% 3.96/1.02    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 3.96/1.02    inference(equality_resolution,[],[f42])).
% 3.96/1.02  
% 3.96/1.02  fof(f10,conjecture,(
% 3.96/1.02    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f11,negated_conjecture,(
% 3.96/1.02    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.96/1.02    inference(negated_conjecture,[],[f10])).
% 3.96/1.02  
% 3.96/1.02  fof(f20,plain,(
% 3.96/1.02    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.96/1.02    inference(ennf_transformation,[],[f11])).
% 3.96/1.02  
% 3.96/1.02  fof(f31,plain,(
% 3.96/1.02    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.96/1.02    inference(nnf_transformation,[],[f20])).
% 3.96/1.02  
% 3.96/1.02  fof(f32,plain,(
% 3.96/1.02    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 3.96/1.02    inference(flattening,[],[f31])).
% 3.96/1.02  
% 3.96/1.02  fof(f33,plain,(
% 3.96/1.02    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK5),sK4) | k1_xboole_0 != k7_relat_1(sK5,sK4)) & (r1_xboole_0(k1_relat_1(sK5),sK4) | k1_xboole_0 = k7_relat_1(sK5,sK4)) & v1_relat_1(sK5))),
% 3.96/1.02    introduced(choice_axiom,[])).
% 3.96/1.02  
% 3.96/1.02  fof(f34,plain,(
% 3.96/1.02    (~r1_xboole_0(k1_relat_1(sK5),sK4) | k1_xboole_0 != k7_relat_1(sK5,sK4)) & (r1_xboole_0(k1_relat_1(sK5),sK4) | k1_xboole_0 = k7_relat_1(sK5,sK4)) & v1_relat_1(sK5)),
% 3.96/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f33])).
% 3.96/1.02  
% 3.96/1.02  fof(f54,plain,(
% 3.96/1.02    r1_xboole_0(k1_relat_1(sK5),sK4) | k1_xboole_0 = k7_relat_1(sK5,sK4)),
% 3.96/1.02    inference(cnf_transformation,[],[f34])).
% 3.96/1.02  
% 3.96/1.02  fof(f43,plain,(
% 3.96/1.02    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f28])).
% 3.96/1.02  
% 3.96/1.02  fof(f6,axiom,(
% 3.96/1.02    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f16,plain,(
% 3.96/1.02    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.96/1.02    inference(ennf_transformation,[],[f6])).
% 3.96/1.02  
% 3.96/1.02  fof(f45,plain,(
% 3.96/1.02    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f16])).
% 3.96/1.02  
% 3.96/1.02  fof(f8,axiom,(
% 3.96/1.02    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f17,plain,(
% 3.96/1.02    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.96/1.02    inference(ennf_transformation,[],[f8])).
% 3.96/1.02  
% 3.96/1.02  fof(f18,plain,(
% 3.96/1.02    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.96/1.02    inference(flattening,[],[f17])).
% 3.96/1.02  
% 3.96/1.02  fof(f48,plain,(
% 3.96/1.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f18])).
% 3.96/1.02  
% 3.96/1.02  fof(f36,plain,(
% 3.96/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f22])).
% 3.96/1.02  
% 3.96/1.02  fof(f37,plain,(
% 3.96/1.02    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.96/1.02    inference(cnf_transformation,[],[f22])).
% 3.96/1.02  
% 3.96/1.02  fof(f7,axiom,(
% 3.96/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.96/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.02  
% 3.96/1.02  fof(f46,plain,(
% 3.96/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.96/1.02    inference(cnf_transformation,[],[f7])).
% 3.96/1.02  
% 3.96/1.02  fof(f55,plain,(
% 3.96/1.02    ~r1_xboole_0(k1_relat_1(sK5),sK4) | k1_xboole_0 != k7_relat_1(sK5,sK4)),
% 3.96/1.02    inference(cnf_transformation,[],[f34])).
% 3.96/1.02  
% 3.96/1.02  fof(f53,plain,(
% 3.96/1.02    v1_relat_1(sK5)),
% 3.96/1.02    inference(cnf_transformation,[],[f34])).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1,plain,
% 3.96/1.02      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.96/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_5851,plain,
% 3.96/1.02      ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),X0)
% 3.96/1.02      | ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK4)
% 3.96/1.02      | ~ r1_xboole_0(X0,sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_8102,plain,
% 3.96/1.02      ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(sK5))
% 3.96/1.02      | ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK4)
% 3.96/1.02      | ~ r1_xboole_0(k1_relat_1(sK5),sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_5851]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_262,plain,
% 3.96/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.96/1.02      theory(equality) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_2141,plain,
% 3.96/1.02      ( r2_hidden(X0,X1)
% 3.96/1.02      | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(sK5,sK4)))
% 3.96/1.02      | X0 != sK0(k1_relat_1(sK5),sK4)
% 3.96/1.02      | X1 != k1_relat_1(k7_relat_1(sK5,sK4)) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_262]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_6475,plain,
% 3.96/1.02      ( r2_hidden(sK0(k1_relat_1(sK5),sK4),X0)
% 3.96/1.02      | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(sK5,sK4)))
% 3.96/1.02      | X0 != k1_relat_1(k7_relat_1(sK5,sK4))
% 3.96/1.02      | sK0(k1_relat_1(sK5),sK4) != sK0(k1_relat_1(sK5),sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_2141]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_6478,plain,
% 3.96/1.02      ( ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(sK5,sK4)))
% 3.96/1.02      | r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_xboole_0)
% 3.96/1.02      | sK0(k1_relat_1(sK5),sK4) != sK0(k1_relat_1(sK5),sK4)
% 3.96/1.02      | k1_xboole_0 != k1_relat_1(k7_relat_1(sK5,sK4)) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_6475]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_260,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1912,plain,
% 3.96/1.02      ( k1_relat_1(X0) != X1
% 3.96/1.02      | k1_xboole_0 != X1
% 3.96/1.02      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_260]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_4896,plain,
% 3.96/1.02      ( k1_relat_1(k7_relat_1(sK5,sK4)) != X0
% 3.96/1.02      | k1_xboole_0 != X0
% 3.96/1.02      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK4)) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1912]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_4897,plain,
% 3.96/1.02      ( k1_relat_1(k7_relat_1(sK5,sK4)) != k1_xboole_0
% 3.96/1.02      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK5,sK4))
% 3.96/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_4896]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_4,plain,
% 3.96/1.02      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.96/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_3625,plain,
% 3.96/1.02      ( r1_xboole_0(sK4,k1_xboole_0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_259,plain,( X0 = X0 ),theory(equality) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_3339,plain,
% 3.96/1.02      ( sK0(k1_relat_1(sK5),sK4) = sK0(k1_relat_1(sK5),sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_259]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_17,plain,
% 3.96/1.02      ( r2_hidden(X0,X1)
% 3.96/1.02      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 3.96/1.02      | ~ v1_relat_1(X2) ),
% 3.96/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_906,plain,
% 3.96/1.02      ( r2_hidden(X0,X1)
% 3.96/1.02      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK5,X1)))
% 3.96/1.02      | ~ v1_relat_1(sK5) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_2349,plain,
% 3.96/1.02      ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(k7_relat_1(sK5,sK4)))
% 3.96/1.02      | r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK4)
% 3.96/1.02      | ~ v1_relat_1(sK5) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_906]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_16,plain,
% 3.96/1.02      ( r2_hidden(X0,k1_relat_1(X1))
% 3.96/1.02      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 3.96/1.02      | ~ v1_relat_1(X1) ),
% 3.96/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_901,plain,
% 3.96/1.02      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK5,X1)))
% 3.96/1.02      | r2_hidden(X0,k1_relat_1(sK5))
% 3.96/1.02      | ~ v1_relat_1(sK5) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_16]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_2350,plain,
% 3.96/1.02      ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(k7_relat_1(sK5,sK4)))
% 3.96/1.02      | r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(sK5))
% 3.96/1.02      | ~ v1_relat_1(sK5) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_901]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1913,plain,
% 3.96/1.02      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.96/1.02      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 3.96/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1912]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_15,plain,
% 3.96/1.02      ( ~ r2_hidden(X0,X1)
% 3.96/1.02      | ~ r2_hidden(X0,k1_relat_1(X2))
% 3.96/1.02      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 3.96/1.02      | ~ v1_relat_1(X2) ),
% 3.96/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1163,plain,
% 3.96/1.02      ( ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(X0))
% 3.96/1.02      | r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(X0,sK4)))
% 3.96/1.02      | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
% 3.96/1.02      | ~ v1_relat_1(X0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1603,plain,
% 3.96/1.02      ( r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(k7_relat_1(sK5,sK4)))
% 3.96/1.02      | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(sK5))
% 3.96/1.02      | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
% 3.96/1.02      | ~ v1_relat_1(sK5) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1163]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_0,plain,
% 3.96/1.02      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.96/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1489,plain,
% 3.96/1.02      ( r1_xboole_0(X0,sK4) | ~ r1_xboole_0(sK4,X0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1491,plain,
% 3.96/1.02      ( ~ r1_xboole_0(sK4,k1_xboole_0) | r1_xboole_0(k1_xboole_0,sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1489]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_263,plain,
% 3.96/1.02      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.96/1.02      theory(equality) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1477,plain,
% 3.96/1.02      ( k7_relat_1(sK5,sK4) != X0
% 3.96/1.02      | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_relat_1(X0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_263]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1479,plain,
% 3.96/1.02      ( k7_relat_1(sK5,sK4) != k1_xboole_0
% 3.96/1.02      | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_relat_1(k1_xboole_0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1477]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1045,plain,
% 3.96/1.02      ( k1_relat_1(k7_relat_1(sK5,sK4)) != X0
% 3.96/1.02      | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_xboole_0
% 3.96/1.02      | k1_xboole_0 != X0 ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_260]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1476,plain,
% 3.96/1.02      ( k1_relat_1(k7_relat_1(sK5,sK4)) != k1_relat_1(X0)
% 3.96/1.02      | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_xboole_0
% 3.96/1.02      | k1_xboole_0 != k1_relat_1(X0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1045]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1478,plain,
% 3.96/1.02      ( k1_relat_1(k7_relat_1(sK5,sK4)) != k1_relat_1(k1_xboole_0)
% 3.96/1.02      | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_xboole_0
% 3.96/1.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1476]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_8,plain,
% 3.96/1.02      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 3.96/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1464,plain,
% 3.96/1.02      ( ~ r2_hidden(k4_tarski(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK2(k7_relat_1(sK5,sK4),k1_xboole_0)),k7_relat_1(sK5,sK4))
% 3.96/1.02      | r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_relat_1(k7_relat_1(sK5,sK4))) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1166,plain,
% 3.96/1.02      ( ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),X0)
% 3.96/1.02      | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
% 3.96/1.02      | ~ r1_xboole_0(X0,sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1171,plain,
% 3.96/1.02      ( ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
% 3.96/1.02      | ~ r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_xboole_0)
% 3.96/1.02      | ~ r1_xboole_0(k1_xboole_0,sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1166]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1116,plain,
% 3.96/1.02      ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),X0)
% 3.96/1.02      | ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
% 3.96/1.02      | ~ r1_xboole_0(X0,k1_xboole_0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1121,plain,
% 3.96/1.02      ( ~ r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
% 3.96/1.02      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_1116]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_19,negated_conjecture,
% 3.96/1.02      ( r1_xboole_0(k1_relat_1(sK5),sK4)
% 3.96/1.02      | k1_xboole_0 = k7_relat_1(sK5,sK4) ),
% 3.96/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_720,plain,
% 3.96/1.02      ( k1_xboole_0 = k7_relat_1(sK5,sK4)
% 3.96/1.02      | r1_xboole_0(k1_relat_1(sK5),sK4) = iProver_top ),
% 3.96/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_737,plain,
% 3.96/1.02      ( r1_xboole_0(X0,X1) != iProver_top
% 3.96/1.02      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.96/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_991,plain,
% 3.96/1.02      ( k7_relat_1(sK5,sK4) = k1_xboole_0
% 3.96/1.02      | r1_xboole_0(sK4,k1_relat_1(sK5)) = iProver_top ),
% 3.96/1.02      inference(superposition,[status(thm)],[c_720,c_737]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1101,plain,
% 3.96/1.02      ( k7_relat_1(sK5,sK4) = k1_xboole_0
% 3.96/1.02      | r1_xboole_0(k1_relat_1(sK5),sK4) = iProver_top ),
% 3.96/1.02      inference(superposition,[status(thm)],[c_991,c_737]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1102,plain,
% 3.96/1.02      ( r1_xboole_0(k1_relat_1(sK5),sK4)
% 3.96/1.02      | k7_relat_1(sK5,sK4) = k1_xboole_0 ),
% 3.96/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1101]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_7,plain,
% 3.96/1.02      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 3.96/1.02      | r2_hidden(sK1(X0,X1),X1)
% 3.96/1.02      | k1_relat_1(X0) = X1 ),
% 3.96/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1037,plain,
% 3.96/1.02      ( r2_hidden(k4_tarski(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),sK2(k7_relat_1(sK5,sK4),k1_xboole_0)),k7_relat_1(sK5,sK4))
% 3.96/1.02      | r2_hidden(sK1(k7_relat_1(sK5,sK4),k1_xboole_0),k1_xboole_0)
% 3.96/1.02      | k1_relat_1(k7_relat_1(sK5,sK4)) = k1_xboole_0 ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_10,plain,
% 3.96/1.02      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.96/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_873,plain,
% 3.96/1.02      ( v1_relat_1(k7_relat_1(sK5,X0)) | ~ v1_relat_1(sK5) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_1000,plain,
% 3.96/1.02      ( v1_relat_1(k7_relat_1(sK5,sK4)) | ~ v1_relat_1(sK5) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_873]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_14,plain,
% 3.96/1.02      ( ~ v1_relat_1(X0)
% 3.96/1.02      | k1_relat_1(X0) != k1_xboole_0
% 3.96/1.02      | k1_xboole_0 = X0 ),
% 3.96/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_924,plain,
% 3.96/1.02      ( ~ v1_relat_1(k7_relat_1(sK5,sK4))
% 3.96/1.02      | k1_relat_1(k7_relat_1(sK5,sK4)) != k1_xboole_0
% 3.96/1.02      | k1_xboole_0 = k7_relat_1(sK5,sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_3,plain,
% 3.96/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.96/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_894,plain,
% 3.96/1.02      ( r2_hidden(sK0(k1_relat_1(sK5),sK4),k1_relat_1(sK5))
% 3.96/1.02      | r1_xboole_0(k1_relat_1(sK5),sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_2,plain,
% 3.96/1.02      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.96/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_891,plain,
% 3.96/1.02      ( r2_hidden(sK0(k1_relat_1(sK5),sK4),sK4)
% 3.96/1.02      | r1_xboole_0(k1_relat_1(sK5),sK4) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_276,plain,
% 3.96/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_259]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_54,plain,
% 3.96/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.96/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_12,plain,
% 3.96/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.96/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_18,negated_conjecture,
% 3.96/1.02      ( ~ r1_xboole_0(k1_relat_1(sK5),sK4)
% 3.96/1.02      | k1_xboole_0 != k7_relat_1(sK5,sK4) ),
% 3.96/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(c_20,negated_conjecture,
% 3.96/1.02      ( v1_relat_1(sK5) ),
% 3.96/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.96/1.02  
% 3.96/1.02  cnf(contradiction,plain,
% 3.96/1.02      ( $false ),
% 3.96/1.02      inference(minisat,
% 3.96/1.02                [status(thm)],
% 3.96/1.02                [c_8102,c_6478,c_4897,c_3625,c_3339,c_2349,c_2350,c_1913,
% 3.96/1.02                 c_1603,c_1491,c_1479,c_1478,c_1464,c_1171,c_1121,c_1102,
% 3.96/1.02                 c_1037,c_1000,c_924,c_894,c_891,c_276,c_54,c_12,c_18,
% 3.96/1.02                 c_20]) ).
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/1.02  
% 3.96/1.02  ------                               Statistics
% 3.96/1.02  
% 3.96/1.02  ------ General
% 3.96/1.02  
% 3.96/1.02  abstr_ref_over_cycles:                  0
% 3.96/1.02  abstr_ref_under_cycles:                 0
% 3.96/1.02  gc_basic_clause_elim:                   0
% 3.96/1.02  forced_gc_time:                         0
% 3.96/1.02  parsing_time:                           0.005
% 3.96/1.02  unif_index_cands_time:                  0.
% 3.96/1.02  unif_index_add_time:                    0.
% 3.96/1.02  orderings_time:                         0.
% 3.96/1.02  out_proof_time:                         0.006
% 3.96/1.02  total_time:                             0.319
% 3.96/1.02  num_of_symbols:                         46
% 3.96/1.02  num_of_terms:                           11982
% 3.96/1.02  
% 3.96/1.02  ------ Preprocessing
% 3.96/1.02  
% 3.96/1.02  num_of_splits:                          0
% 3.96/1.02  num_of_split_atoms:                     0
% 3.96/1.02  num_of_reused_defs:                     0
% 3.96/1.02  num_eq_ax_congr_red:                    18
% 3.96/1.02  num_of_sem_filtered_clauses:            1
% 3.96/1.02  num_of_subtypes:                        0
% 3.96/1.02  monotx_restored_types:                  0
% 3.96/1.02  sat_num_of_epr_types:                   0
% 3.96/1.02  sat_num_of_non_cyclic_types:            0
% 3.96/1.02  sat_guarded_non_collapsed_types:        0
% 3.96/1.02  num_pure_diseq_elim:                    0
% 3.96/1.02  simp_replaced_by:                       0
% 3.96/1.02  res_preprocessed:                       82
% 3.96/1.02  prep_upred:                             0
% 3.96/1.02  prep_unflattend:                        0
% 3.96/1.02  smt_new_axioms:                         0
% 3.96/1.02  pred_elim_cands:                        3
% 3.96/1.02  pred_elim:                              0
% 3.96/1.02  pred_elim_cl:                           0
% 3.96/1.02  pred_elim_cycles:                       1
% 3.96/1.02  merged_defs:                            6
% 3.96/1.02  merged_defs_ncl:                        0
% 3.96/1.02  bin_hyper_res:                          6
% 3.96/1.02  prep_cycles:                            3
% 3.96/1.02  pred_elim_time:                         0.
% 3.96/1.02  splitting_time:                         0.
% 3.96/1.02  sem_filter_time:                        0.
% 3.96/1.02  monotx_time:                            0.
% 3.96/1.02  subtype_inf_time:                       0.
% 3.96/1.02  
% 3.96/1.02  ------ Problem properties
% 3.96/1.02  
% 3.96/1.02  clauses:                                21
% 3.96/1.02  conjectures:                            3
% 3.96/1.02  epr:                                    4
% 3.96/1.02  horn:                                   17
% 3.96/1.02  ground:                                 5
% 3.96/1.02  unary:                                  4
% 3.96/1.02  binary:                                 9
% 3.96/1.02  lits:                                   47
% 3.96/1.02  lits_eq:                                10
% 3.96/1.02  fd_pure:                                0
% 3.96/1.02  fd_pseudo:                              0
% 3.96/1.02  fd_cond:                                2
% 3.96/1.02  fd_pseudo_cond:                         2
% 3.96/1.02  ac_symbols:                             0
% 3.96/1.02  
% 3.96/1.02  ------ Propositional Solver
% 3.96/1.02  
% 3.96/1.02  prop_solver_calls:                      28
% 3.96/1.02  prop_fast_solver_calls:                 835
% 3.96/1.02  smt_solver_calls:                       0
% 3.96/1.02  smt_fast_solver_calls:                  0
% 3.96/1.02  prop_num_of_clauses:                    4094
% 3.96/1.02  prop_preprocess_simplified:             6136
% 3.96/1.02  prop_fo_subsumed:                       13
% 3.96/1.02  prop_solver_time:                       0.
% 3.96/1.02  smt_solver_time:                        0.
% 3.96/1.02  smt_fast_solver_time:                   0.
% 3.96/1.02  prop_fast_solver_time:                  0.
% 3.96/1.02  prop_unsat_core_time:                   0.
% 3.96/1.02  
% 3.96/1.02  ------ QBF
% 3.96/1.02  
% 3.96/1.02  qbf_q_res:                              0
% 3.96/1.02  qbf_num_tautologies:                    0
% 3.96/1.02  qbf_prep_cycles:                        0
% 3.96/1.02  
% 3.96/1.02  ------ BMC1
% 3.96/1.02  
% 3.96/1.02  bmc1_current_bound:                     -1
% 3.96/1.02  bmc1_last_solved_bound:                 -1
% 3.96/1.02  bmc1_unsat_core_size:                   -1
% 3.96/1.02  bmc1_unsat_core_parents_size:           -1
% 3.96/1.02  bmc1_merge_next_fun:                    0
% 3.96/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.96/1.02  
% 3.96/1.02  ------ Instantiation
% 3.96/1.02  
% 3.96/1.02  inst_num_of_clauses:                    874
% 3.96/1.02  inst_num_in_passive:                    353
% 3.96/1.02  inst_num_in_active:                     521
% 3.96/1.02  inst_num_in_unprocessed:                0
% 3.96/1.02  inst_num_of_loops:                      777
% 3.96/1.02  inst_num_of_learning_restarts:          0
% 3.96/1.02  inst_num_moves_active_passive:          249
% 3.96/1.02  inst_lit_activity:                      0
% 3.96/1.02  inst_lit_activity_moves:                0
% 3.96/1.02  inst_num_tautologies:                   0
% 3.96/1.02  inst_num_prop_implied:                  0
% 3.96/1.02  inst_num_existing_simplified:           0
% 3.96/1.02  inst_num_eq_res_simplified:             0
% 3.96/1.02  inst_num_child_elim:                    0
% 3.96/1.02  inst_num_of_dismatching_blockings:      202
% 3.96/1.02  inst_num_of_non_proper_insts:           806
% 3.96/1.02  inst_num_of_duplicates:                 0
% 3.96/1.02  inst_inst_num_from_inst_to_res:         0
% 3.96/1.02  inst_dismatching_checking_time:         0.
% 3.96/1.02  
% 3.96/1.02  ------ Resolution
% 3.96/1.02  
% 3.96/1.02  res_num_of_clauses:                     0
% 3.96/1.02  res_num_in_passive:                     0
% 3.96/1.02  res_num_in_active:                      0
% 3.96/1.02  res_num_of_loops:                       85
% 3.96/1.02  res_forward_subset_subsumed:            45
% 3.96/1.02  res_backward_subset_subsumed:           4
% 3.96/1.02  res_forward_subsumed:                   0
% 3.96/1.02  res_backward_subsumed:                  0
% 3.96/1.02  res_forward_subsumption_resolution:     0
% 3.96/1.02  res_backward_subsumption_resolution:    0
% 3.96/1.02  res_clause_to_clause_subsumption:       2378
% 3.96/1.02  res_orphan_elimination:                 0
% 3.96/1.02  res_tautology_del:                      86
% 3.96/1.02  res_num_eq_res_simplified:              0
% 3.96/1.02  res_num_sel_changes:                    0
% 3.96/1.02  res_moves_from_active_to_pass:          0
% 3.96/1.02  
% 3.96/1.02  ------ Superposition
% 3.96/1.02  
% 3.96/1.02  sup_time_total:                         0.
% 3.96/1.02  sup_time_generating:                    0.
% 3.96/1.02  sup_time_sim_full:                      0.
% 3.96/1.02  sup_time_sim_immed:                     0.
% 3.96/1.02  
% 3.96/1.02  sup_num_of_clauses:                     449
% 3.96/1.02  sup_num_in_active:                      130
% 3.96/1.02  sup_num_in_passive:                     319
% 3.96/1.02  sup_num_of_loops:                       154
% 3.96/1.02  sup_fw_superposition:                   855
% 3.96/1.02  sup_bw_superposition:                   519
% 3.96/1.02  sup_immediate_simplified:               508
% 3.96/1.02  sup_given_eliminated:                   0
% 3.96/1.02  comparisons_done:                       0
% 3.96/1.02  comparisons_avoided:                    0
% 3.96/1.02  
% 3.96/1.02  ------ Simplifications
% 3.96/1.02  
% 3.96/1.02  
% 3.96/1.02  sim_fw_subset_subsumed:                 50
% 3.96/1.02  sim_bw_subset_subsumed:                 11
% 3.96/1.02  sim_fw_subsumed:                        192
% 3.96/1.02  sim_bw_subsumed:                        1
% 3.96/1.02  sim_fw_subsumption_res:                 19
% 3.96/1.02  sim_bw_subsumption_res:                 0
% 3.96/1.02  sim_tautology_del:                      38
% 3.96/1.02  sim_eq_tautology_del:                   32
% 3.96/1.02  sim_eq_res_simp:                        0
% 3.96/1.02  sim_fw_demodulated:                     303
% 3.96/1.02  sim_bw_demodulated:                     15
% 3.96/1.02  sim_light_normalised:                   299
% 3.96/1.02  sim_joinable_taut:                      0
% 3.96/1.02  sim_joinable_simp:                      0
% 3.96/1.02  sim_ac_normalised:                      0
% 3.96/1.02  sim_smt_subsumption:                    0
% 3.96/1.02  
%------------------------------------------------------------------------------

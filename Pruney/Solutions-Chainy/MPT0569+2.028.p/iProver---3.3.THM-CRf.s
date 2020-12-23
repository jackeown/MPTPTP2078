%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:31 EST 2020

% Result     : Theorem 19.61s
% Output     : CNFRefutation 19.61s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 631 expanded)
%              Number of clauses        :   71 ( 239 expanded)
%              Number of leaves         :   17 ( 179 expanded)
%              Depth                    :   24
%              Number of atoms          :  366 (2314 expanded)
%              Number of equality atoms :   70 ( 526 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 != k10_relat_1(sK6,sK5) )
      & ( r1_xboole_0(k2_relat_1(sK6),sK5)
        | k1_xboole_0 = k10_relat_1(sK6,sK5) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 != k10_relat_1(sK6,sK5) )
    & ( r1_xboole_0(k2_relat_1(sK6),sK5)
      | k1_xboole_0 = k10_relat_1(sK6,sK5) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f29])).

fof(f46,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f9,plain,(
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

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(X0,k2_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_79744,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8,c_10])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_83942,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | r2_hidden(sK3(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(resolution,[status(thm)],[c_79744,c_9])).

cnf(c_204,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_81582,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
    | r2_hidden(X1,k1_xboole_0)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_204,c_15])).

cnf(c_202,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_201,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_68674,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_202,c_201])).

cnf(c_69662,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68674,c_15])).

cnf(c_203,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_68835,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_203,c_201])).

cnf(c_70119,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | ~ r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_69662,c_68835])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2760,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_4])).

cnf(c_3144,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_202,c_201])).

cnf(c_4363,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3144,c_15])).

cnf(c_3158,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_203,c_201])).

cnf(c_4577,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | ~ r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_4363,c_3158])).

cnf(c_70355,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | r1_xboole_0(k10_relat_1(sK6,sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_70119,c_2760,c_4577])).

cnf(c_70356,plain,
    ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(renaming,[status(thm)],[c_70355])).

cnf(c_70371,plain,
    ( r1_xboole_0(X0,k10_relat_1(sK6,sK5))
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(resolution,[status(thm)],[c_70356,c_0])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_71787,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(resolution,[status(thm)],[c_70371,c_5])).

cnf(c_82447,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | ~ r2_hidden(X0,k10_relat_1(sK6,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_81582,c_71787])).

cnf(c_82448,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
    | r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(renaming,[status(thm)],[c_82447])).

cnf(c_86175,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(X0,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_83942,c_82448])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_19925,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | ~ r1_xboole_0(k2_relat_1(X2),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_55159,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(X0,sK5)
    | ~ r1_xboole_0(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_19925])).

cnf(c_68434,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8,c_10])).

cnf(c_70885,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_relat_1(X2))
    | r2_hidden(sK3(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(resolution,[status(thm)],[c_68434,c_9])).

cnf(c_74047,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(X0,sK5)
    | r1_xboole_0(k2_relat_1(sK6),sK5)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_71787,c_70885])).

cnf(c_86431,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ r2_hidden(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_86175,c_16,c_55159,c_74047])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_86630,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | ~ r2_hidden(sK4(X0,X1,sK6),sK5)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_86431,c_13])).

cnf(c_89974,plain,
    ( ~ r2_hidden(sK4(X0,X1,sK6),sK5)
    | ~ r2_hidden(X0,k10_relat_1(sK6,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_86630,c_16])).

cnf(c_89975,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
    | ~ r2_hidden(sK4(X0,X1,sK6),sK5) ),
    inference(renaming,[status(thm)],[c_89974])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_89992,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_89975,c_11])).

cnf(c_96239,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_89992,c_16])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_79732,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5,c_4])).

cnf(c_82031,plain,
    ( r2_hidden(sK1(k1_xboole_0,X0),X0)
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_7,c_79732])).

cnf(c_79963,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_202,c_201])).

cnf(c_84511,plain,
    ( r2_hidden(sK1(k1_xboole_0,X0),X0)
    | X0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_82031,c_79963])).

cnf(c_84526,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k2_relat_1(k1_xboole_0) = k10_relat_1(sK6,sK5) ),
    inference(resolution,[status(thm)],[c_82031,c_82448])).

cnf(c_79961,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | X0 != k10_relat_1(sK6,sK5)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_202,c_15])).

cnf(c_84566,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_84526,c_79961])).

cnf(c_21177,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_56680,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21177])).

cnf(c_56681,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_56680])).

cnf(c_58180,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_56681])).

cnf(c_68420,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5,c_4])).

cnf(c_69917,plain,
    ( r2_hidden(sK1(k1_xboole_0,X0),X0)
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_7,c_68420])).

cnf(c_71129,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69917,c_68420])).

cnf(c_85018,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_84566,c_58180,c_71129])).

cnf(c_85025,plain,
    ( X0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_85018,c_202])).

cnf(c_88291,plain,
    ( r2_hidden(sK1(k1_xboole_0,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_84511,c_85025])).

cnf(c_96286,plain,
    ( k1_xboole_0 = k10_relat_1(sK6,sK5) ),
    inference(resolution,[status(thm)],[c_96239,c_88291])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_86604,plain,
    ( ~ r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5)
    | r1_xboole_0(X0,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_86431,c_2])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_86732,plain,
    ( r1_xboole_0(sK5,k2_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_86604,c_3])).

cnf(c_2729,plain,
    ( r1_xboole_0(k2_relat_1(sK6),sK5)
    | ~ r1_xboole_0(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
    | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96286,c_86732,c_2729,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 19.61/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.61/3.00  
% 19.61/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.61/3.00  
% 19.61/3.00  ------  iProver source info
% 19.61/3.00  
% 19.61/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.61/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.61/3.00  git: non_committed_changes: false
% 19.61/3.00  git: last_make_outside_of_git: false
% 19.61/3.00  
% 19.61/3.00  ------ 
% 19.61/3.00  ------ Parsing...
% 19.61/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.61/3.00  ------ Proving...
% 19.61/3.00  ------ Problem Properties 
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  clauses                                 17
% 19.61/3.00  conjectures                             3
% 19.61/3.00  EPR                                     4
% 19.61/3.00  Horn                                    13
% 19.61/3.00  unary                                   2
% 19.61/3.00  binary                                  8
% 19.61/3.00  lits                                    41
% 19.61/3.00  lits eq                                 4
% 19.61/3.00  fd_pure                                 0
% 19.61/3.00  fd_pseudo                               0
% 19.61/3.00  fd_cond                                 0
% 19.61/3.00  fd_pseudo_cond                          2
% 19.61/3.00  AC symbols                              0
% 19.61/3.00  
% 19.61/3.00  ------ Input Options Time Limit: Unbounded
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 19.61/3.00  Current options:
% 19.61/3.00  ------ 
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Proving...
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.61/3.00  
% 19.61/3.00  ------ Proving...
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.61/3.00  
% 19.61/3.00  ------ Proving...
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.61/3.00  
% 19.61/3.00  ------ Proving...
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.61/3.00  
% 19.61/3.00  ------ Proving...
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.61/3.00  
% 19.61/3.00  ------ Proving...
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.61/3.00  
% 19.61/3.00  ------ Proving...
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.61/3.00  
% 19.61/3.00  ------ Proving...
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  % SZS status Theorem for theBenchmark.p
% 19.61/3.00  
% 19.61/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.61/3.00  
% 19.61/3.00  fof(f5,axiom,(
% 19.61/3.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 19.61/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/3.00  
% 19.61/3.00  fof(f17,plain,(
% 19.61/3.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 19.61/3.00    inference(nnf_transformation,[],[f5])).
% 19.61/3.00  
% 19.61/3.00  fof(f18,plain,(
% 19.61/3.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 19.61/3.00    inference(rectify,[],[f17])).
% 19.61/3.00  
% 19.61/3.00  fof(f21,plain,(
% 19.61/3.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 19.61/3.00    introduced(choice_axiom,[])).
% 19.61/3.00  
% 19.61/3.00  fof(f20,plain,(
% 19.61/3.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0))) )),
% 19.61/3.00    introduced(choice_axiom,[])).
% 19.61/3.00  
% 19.61/3.00  fof(f19,plain,(
% 19.61/3.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 19.61/3.00    introduced(choice_axiom,[])).
% 19.61/3.00  
% 19.61/3.00  fof(f22,plain,(
% 19.61/3.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 19.61/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f21,f20,f19])).
% 19.61/3.00  
% 19.61/3.00  fof(f38,plain,(
% 19.61/3.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 19.61/3.00    inference(cnf_transformation,[],[f22])).
% 19.61/3.00  
% 19.61/3.00  fof(f48,plain,(
% 19.61/3.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 19.61/3.00    inference(equality_resolution,[],[f38])).
% 19.61/3.00  
% 19.61/3.00  fof(f6,axiom,(
% 19.61/3.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 19.61/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/3.00  
% 19.61/3.00  fof(f13,plain,(
% 19.61/3.00    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 19.61/3.00    inference(ennf_transformation,[],[f6])).
% 19.61/3.00  
% 19.61/3.00  fof(f23,plain,(
% 19.61/3.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.61/3.00    inference(nnf_transformation,[],[f13])).
% 19.61/3.00  
% 19.61/3.00  fof(f24,plain,(
% 19.61/3.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.61/3.00    inference(rectify,[],[f23])).
% 19.61/3.00  
% 19.61/3.00  fof(f25,plain,(
% 19.61/3.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 19.61/3.00    introduced(choice_axiom,[])).
% 19.61/3.00  
% 19.61/3.00  fof(f26,plain,(
% 19.61/3.00    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 19.61/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 19.61/3.00  
% 19.61/3.00  fof(f44,plain,(
% 19.61/3.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f26])).
% 19.61/3.00  
% 19.61/3.00  fof(f37,plain,(
% 19.61/3.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 19.61/3.00    inference(cnf_transformation,[],[f22])).
% 19.61/3.00  
% 19.61/3.00  fof(f49,plain,(
% 19.61/3.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 19.61/3.00    inference(equality_resolution,[],[f37])).
% 19.61/3.00  
% 19.61/3.00  fof(f7,conjecture,(
% 19.61/3.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 19.61/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/3.00  
% 19.61/3.00  fof(f8,negated_conjecture,(
% 19.61/3.00    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 19.61/3.00    inference(negated_conjecture,[],[f7])).
% 19.61/3.00  
% 19.61/3.00  fof(f14,plain,(
% 19.61/3.00    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 19.61/3.00    inference(ennf_transformation,[],[f8])).
% 19.61/3.00  
% 19.61/3.00  fof(f27,plain,(
% 19.61/3.00    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 19.61/3.00    inference(nnf_transformation,[],[f14])).
% 19.61/3.00  
% 19.61/3.00  fof(f28,plain,(
% 19.61/3.00    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 19.61/3.00    inference(flattening,[],[f27])).
% 19.61/3.00  
% 19.61/3.00  fof(f29,plain,(
% 19.61/3.00    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6))),
% 19.61/3.00    introduced(choice_axiom,[])).
% 19.61/3.00  
% 19.61/3.00  fof(f30,plain,(
% 19.61/3.00    (~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)) & (r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)) & v1_relat_1(sK6)),
% 19.61/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f29])).
% 19.61/3.00  
% 19.61/3.00  fof(f46,plain,(
% 19.61/3.00    r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 = k10_relat_1(sK6,sK5)),
% 19.61/3.00    inference(cnf_transformation,[],[f30])).
% 19.61/3.00  
% 19.61/3.00  fof(f1,axiom,(
% 19.61/3.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 19.61/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/3.00  
% 19.61/3.00  fof(f10,plain,(
% 19.61/3.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 19.61/3.00    inference(ennf_transformation,[],[f1])).
% 19.61/3.00  
% 19.61/3.00  fof(f31,plain,(
% 19.61/3.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f10])).
% 19.61/3.00  
% 19.61/3.00  fof(f3,axiom,(
% 19.61/3.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 19.61/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/3.00  
% 19.61/3.00  fof(f35,plain,(
% 19.61/3.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f3])).
% 19.61/3.00  
% 19.61/3.00  fof(f4,axiom,(
% 19.61/3.00    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 19.61/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/3.00  
% 19.61/3.00  fof(f12,plain,(
% 19.61/3.00    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 19.61/3.00    inference(ennf_transformation,[],[f4])).
% 19.61/3.00  
% 19.61/3.00  fof(f36,plain,(
% 19.61/3.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f12])).
% 19.61/3.00  
% 19.61/3.00  fof(f45,plain,(
% 19.61/3.00    v1_relat_1(sK6)),
% 19.61/3.00    inference(cnf_transformation,[],[f30])).
% 19.61/3.00  
% 19.61/3.00  fof(f2,axiom,(
% 19.61/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.61/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.61/3.00  
% 19.61/3.00  fof(f9,plain,(
% 19.61/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.61/3.00    inference(rectify,[],[f2])).
% 19.61/3.00  
% 19.61/3.00  fof(f11,plain,(
% 19.61/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.61/3.00    inference(ennf_transformation,[],[f9])).
% 19.61/3.00  
% 19.61/3.00  fof(f15,plain,(
% 19.61/3.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.61/3.00    introduced(choice_axiom,[])).
% 19.61/3.00  
% 19.61/3.00  fof(f16,plain,(
% 19.61/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.61/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 19.61/3.00  
% 19.61/3.00  fof(f34,plain,(
% 19.61/3.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f16])).
% 19.61/3.00  
% 19.61/3.00  fof(f41,plain,(
% 19.61/3.00    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f26])).
% 19.61/3.00  
% 19.61/3.00  fof(f43,plain,(
% 19.61/3.00    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f26])).
% 19.61/3.00  
% 19.61/3.00  fof(f39,plain,(
% 19.61/3.00    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f22])).
% 19.61/3.00  
% 19.61/3.00  fof(f33,plain,(
% 19.61/3.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f16])).
% 19.61/3.00  
% 19.61/3.00  fof(f32,plain,(
% 19.61/3.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 19.61/3.00    inference(cnf_transformation,[],[f16])).
% 19.61/3.00  
% 19.61/3.00  fof(f47,plain,(
% 19.61/3.00    ~r1_xboole_0(k2_relat_1(sK6),sK5) | k1_xboole_0 != k10_relat_1(sK6,sK5)),
% 19.61/3.00    inference(cnf_transformation,[],[f30])).
% 19.61/3.00  
% 19.61/3.00  cnf(c_8,plain,
% 19.61/3.00      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 19.61/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_10,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1)
% 19.61/3.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 19.61/3.00      | ~ r2_hidden(X0,k2_relat_1(X3))
% 19.61/3.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 19.61/3.00      | ~ v1_relat_1(X3) ),
% 19.61/3.00      inference(cnf_transformation,[],[f44]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_79744,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1)
% 19.61/3.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 19.61/3.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 19.61/3.00      | ~ v1_relat_1(X3) ),
% 19.61/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_8,c_10]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_9,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 19.61/3.00      | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
% 19.61/3.00      inference(cnf_transformation,[],[f49]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_83942,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1)
% 19.61/3.00      | ~ r2_hidden(X0,k2_relat_1(X2))
% 19.61/3.00      | r2_hidden(sK3(X2,X0),k10_relat_1(X2,X1))
% 19.61/3.00      | ~ v1_relat_1(X2) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_79744,c_9]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_204,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.61/3.00      theory(equality) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_15,negated_conjecture,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 19.61/3.00      inference(cnf_transformation,[],[f46]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_81582,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
% 19.61/3.00      | r2_hidden(X1,k1_xboole_0)
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | X1 != X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_204,c_15]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_202,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_201,plain,( X0 = X0 ),theory(equality) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_68674,plain,
% 19.61/3.00      ( X0 != X1 | X1 = X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_202,c_201]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_69662,plain,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_68674,c_15]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_203,plain,
% 19.61/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.61/3.00      theory(equality) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_68835,plain,
% 19.61/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_203,c_201]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_70119,plain,
% 19.61/3.00      ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | ~ r1_xboole_0(k1_xboole_0,X0) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_69662,c_68835]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_0,plain,
% 19.61/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.61/3.00      inference(cnf_transformation,[],[f31]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_4,plain,
% 19.61/3.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 19.61/3.00      inference(cnf_transformation,[],[f35]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_2760,plain,
% 19.61/3.00      ( r1_xboole_0(k1_xboole_0,X0) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_0,c_4]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_3144,plain,
% 19.61/3.00      ( X0 != X1 | X1 = X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_202,c_201]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_4363,plain,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | k10_relat_1(sK6,sK5) = k1_xboole_0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_3144,c_15]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_3158,plain,
% 19.61/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_203,c_201]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_4577,plain,
% 19.61/3.00      ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | ~ r1_xboole_0(k1_xboole_0,X0) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_4363,c_3158]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_70355,plain,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | r1_xboole_0(k10_relat_1(sK6,sK5),X0) ),
% 19.61/3.00      inference(global_propositional_subsumption,
% 19.61/3.00                [status(thm)],
% 19.61/3.00                [c_70119,c_2760,c_4577]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_70356,plain,
% 19.61/3.00      ( r1_xboole_0(k10_relat_1(sK6,sK5),X0)
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 19.61/3.00      inference(renaming,[status(thm)],[c_70355]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_70371,plain,
% 19.61/3.00      ( r1_xboole_0(X0,k10_relat_1(sK6,sK5))
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_70356,c_0]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_5,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_tarski(X0),X1) ),
% 19.61/3.00      inference(cnf_transformation,[],[f36]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_71787,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_70371,c_5]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_82447,plain,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | ~ r2_hidden(X0,k10_relat_1(sK6,sK5)) ),
% 19.61/3.00      inference(global_propositional_subsumption,
% 19.61/3.00                [status(thm)],
% 19.61/3.00                [c_81582,c_71787]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_82448,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5))
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 19.61/3.00      inference(renaming,[status(thm)],[c_82447]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_86175,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 19.61/3.00      | ~ r2_hidden(X0,sK5)
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | ~ v1_relat_1(sK6) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_83942,c_82448]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_16,negated_conjecture,
% 19.61/3.00      ( v1_relat_1(sK6) ),
% 19.61/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_1,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 19.61/3.00      inference(cnf_transformation,[],[f34]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_19925,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1)
% 19.61/3.00      | ~ r2_hidden(X0,k2_relat_1(X2))
% 19.61/3.00      | ~ r1_xboole_0(k2_relat_1(X2),X1) ),
% 19.61/3.00      inference(instantiation,[status(thm)],[c_1]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_55159,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 19.61/3.00      | ~ r2_hidden(X0,sK5)
% 19.61/3.00      | ~ r1_xboole_0(k2_relat_1(sK6),sK5) ),
% 19.61/3.00      inference(instantiation,[status(thm)],[c_19925]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_68434,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1)
% 19.61/3.00      | r2_hidden(X2,k10_relat_1(X3,X1))
% 19.61/3.00      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 19.61/3.00      | ~ v1_relat_1(X3) ),
% 19.61/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_8,c_10]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_70885,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,X1)
% 19.61/3.00      | ~ r2_hidden(X0,k2_relat_1(X2))
% 19.61/3.00      | r2_hidden(sK3(X2,X0),k10_relat_1(X2,X1))
% 19.61/3.00      | ~ v1_relat_1(X2) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_68434,c_9]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_74047,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 19.61/3.00      | ~ r2_hidden(X0,sK5)
% 19.61/3.00      | r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | ~ v1_relat_1(sK6) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_71787,c_70885]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_86431,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k2_relat_1(sK6)) | ~ r2_hidden(X0,sK5) ),
% 19.61/3.00      inference(global_propositional_subsumption,
% 19.61/3.00                [status(thm)],
% 19.61/3.00                [c_86175,c_16,c_55159,c_74047]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_13,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 19.61/3.00      | r2_hidden(sK4(X0,X2,X1),k2_relat_1(X1))
% 19.61/3.00      | ~ v1_relat_1(X1) ),
% 19.61/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_86630,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 19.61/3.00      | ~ r2_hidden(sK4(X0,X1,sK6),sK5)
% 19.61/3.00      | ~ v1_relat_1(sK6) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_86431,c_13]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_89974,plain,
% 19.61/3.00      ( ~ r2_hidden(sK4(X0,X1,sK6),sK5)
% 19.61/3.00      | ~ r2_hidden(X0,k10_relat_1(sK6,X1)) ),
% 19.61/3.00      inference(global_propositional_subsumption,
% 19.61/3.00                [status(thm)],
% 19.61/3.00                [c_86630,c_16]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_89975,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,X1))
% 19.61/3.00      | ~ r2_hidden(sK4(X0,X1,sK6),sK5) ),
% 19.61/3.00      inference(renaming,[status(thm)],[c_89974]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_11,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 19.61/3.00      | r2_hidden(sK4(X0,X2,X1),X2)
% 19.61/3.00      | ~ v1_relat_1(X1) ),
% 19.61/3.00      inference(cnf_transformation,[],[f43]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_89992,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5)) | ~ v1_relat_1(sK6) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_89975,c_11]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_96239,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k10_relat_1(sK6,sK5)) ),
% 19.61/3.00      inference(global_propositional_subsumption,
% 19.61/3.00                [status(thm)],
% 19.61/3.00                [c_89992,c_16]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_7,plain,
% 19.61/3.00      ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
% 19.61/3.00      | r2_hidden(sK1(X0,X1),X1)
% 19.61/3.00      | k2_relat_1(X0) = X1 ),
% 19.61/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_79732,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_5,c_4]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_82031,plain,
% 19.61/3.00      ( r2_hidden(sK1(k1_xboole_0,X0),X0)
% 19.61/3.00      | k2_relat_1(k1_xboole_0) = X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_7,c_79732]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_79963,plain,
% 19.61/3.00      ( X0 != X1 | X1 = X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_202,c_201]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_84511,plain,
% 19.61/3.00      ( r2_hidden(sK1(k1_xboole_0,X0),X0)
% 19.61/3.00      | X0 = k2_relat_1(k1_xboole_0) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_82031,c_79963]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_84526,plain,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | k2_relat_1(k1_xboole_0) = k10_relat_1(sK6,sK5) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_82031,c_82448]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_79961,plain,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | X0 != k10_relat_1(sK6,sK5)
% 19.61/3.00      | k1_xboole_0 = X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_202,c_15]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_84566,plain,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_84526,c_79961]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_21177,plain,
% 19.61/3.00      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 19.61/3.00      inference(instantiation,[status(thm)],[c_202]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_56680,plain,
% 19.61/3.00      ( X0 != k1_xboole_0
% 19.61/3.00      | k1_xboole_0 = X0
% 19.61/3.00      | k1_xboole_0 != k1_xboole_0 ),
% 19.61/3.00      inference(instantiation,[status(thm)],[c_21177]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_56681,plain,
% 19.61/3.00      ( X0 != k1_xboole_0 | k1_xboole_0 = X0 ),
% 19.61/3.00      inference(equality_resolution_simp,[status(thm)],[c_56680]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_58180,plain,
% 19.61/3.00      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 19.61/3.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 19.61/3.00      inference(instantiation,[status(thm)],[c_56681]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_68420,plain,
% 19.61/3.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_5,c_4]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_69917,plain,
% 19.61/3.00      ( r2_hidden(sK1(k1_xboole_0,X0),X0)
% 19.61/3.00      | k2_relat_1(k1_xboole_0) = X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_7,c_68420]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_71129,plain,
% 19.61/3.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_69917,c_68420]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_85018,plain,
% 19.61/3.00      ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 19.61/3.00      inference(global_propositional_subsumption,
% 19.61/3.00                [status(thm)],
% 19.61/3.00                [c_84566,c_58180,c_71129]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_85025,plain,
% 19.61/3.00      ( X0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_85018,c_202]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_88291,plain,
% 19.61/3.00      ( r2_hidden(sK1(k1_xboole_0,X0),X0) | k1_xboole_0 = X0 ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_84511,c_85025]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_96286,plain,
% 19.61/3.00      ( k1_xboole_0 = k10_relat_1(sK6,sK5) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_96239,c_88291]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_2,plain,
% 19.61/3.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 19.61/3.00      inference(cnf_transformation,[],[f33]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_86604,plain,
% 19.61/3.00      ( ~ r2_hidden(sK0(X0,k2_relat_1(sK6)),sK5)
% 19.61/3.00      | r1_xboole_0(X0,k2_relat_1(sK6)) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_86431,c_2]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_3,plain,
% 19.61/3.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 19.61/3.00      inference(cnf_transformation,[],[f32]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_86732,plain,
% 19.61/3.00      ( r1_xboole_0(sK5,k2_relat_1(sK6)) ),
% 19.61/3.00      inference(resolution,[status(thm)],[c_86604,c_3]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_2729,plain,
% 19.61/3.00      ( r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | ~ r1_xboole_0(sK5,k2_relat_1(sK6)) ),
% 19.61/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(c_14,negated_conjecture,
% 19.61/3.00      ( ~ r1_xboole_0(k2_relat_1(sK6),sK5)
% 19.61/3.00      | k1_xboole_0 != k10_relat_1(sK6,sK5) ),
% 19.61/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.61/3.00  
% 19.61/3.00  cnf(contradiction,plain,
% 19.61/3.00      ( $false ),
% 19.61/3.00      inference(minisat,[status(thm)],[c_96286,c_86732,c_2729,c_14]) ).
% 19.61/3.00  
% 19.61/3.00  
% 19.61/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.61/3.00  
% 19.61/3.00  ------                               Statistics
% 19.61/3.00  
% 19.61/3.00  ------ Selected
% 19.61/3.00  
% 19.61/3.00  total_time:                             2.366
% 19.61/3.00  
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:46 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 231 expanded)
%              Number of clauses        :   49 (  63 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  250 ( 556 expanded)
%              Number of equality atoms :   47 (  99 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f32])).

fof(f53,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f64,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f53,f41,f58])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f41,f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_405,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_404,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2166,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_405,c_404])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3712,plain,
    ( ~ r1_xboole_0(X0,X1)
    | X0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_2166,c_12])).

cnf(c_407,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2183,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_407,c_404])).

cnf(c_4013,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_3712,c_2183])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_240,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X2
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_241,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_983,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_1,c_241])).

cnf(c_4041,plain,
    ( ~ r1_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r1_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4013,c_983])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1313,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[status(thm)],[c_14,c_1])).

cnf(c_4156,plain,
    ( r2_hidden(sK5,X0)
    | r1_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4041,c_1313])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4422,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK5,X1) ),
    inference(resolution,[status(thm)],[c_4156,c_2])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1628,plain,
    ( r2_hidden(X0,sK3)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1634,plain,
    ( r2_hidden(sK5,sK3)
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_992,plain,
    ( ~ r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1670,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_821,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1989,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_821])).

cnf(c_814,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_819,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1090,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_814,c_819])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_826,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3371,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_826])).

cnf(c_3659,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_3371])).

cnf(c_5631,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1989,c_3659])).

cnf(c_5648,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5631])).

cnf(c_6996,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4422,c_17,c_16,c_1634,c_1670,c_5648])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8415,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_6996,c_6])).

cnf(c_1339,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1054,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_981,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1,c_16])).

cnf(c_945,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8415,c_1339,c_1054,c_981,c_945,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.49/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/1.01  
% 3.49/1.01  ------  iProver source info
% 3.49/1.01  
% 3.49/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.49/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/1.01  git: non_committed_changes: false
% 3.49/1.01  git: last_make_outside_of_git: false
% 3.49/1.01  
% 3.49/1.01  ------ 
% 3.49/1.01  ------ Parsing...
% 3.49/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/1.01  
% 3.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/1.01  ------ Proving...
% 3.49/1.01  ------ Problem Properties 
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  clauses                                 18
% 3.49/1.01  conjectures                             3
% 3.49/1.01  EPR                                     4
% 3.49/1.01  Horn                                    14
% 3.49/1.01  unary                                   5
% 3.49/1.01  binary                                  11
% 3.49/1.01  lits                                    33
% 3.49/1.01  lits eq                                 3
% 3.49/1.01  fd_pure                                 0
% 3.49/1.01  fd_pseudo                               0
% 3.49/1.01  fd_cond                                 0
% 3.49/1.01  fd_pseudo_cond                          0
% 3.49/1.01  AC symbols                              0
% 3.49/1.01  
% 3.49/1.01  ------ Input Options Time Limit: Unbounded
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  ------ 
% 3.49/1.01  Current options:
% 3.49/1.01  ------ 
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  ------ Proving...
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  % SZS status Theorem for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  fof(f8,axiom,(
% 3.49/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f31,plain,(
% 3.49/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.49/1.01    inference(nnf_transformation,[],[f8])).
% 3.49/1.01  
% 3.49/1.01  fof(f46,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f31])).
% 3.49/1.01  
% 3.49/1.01  fof(f2,axiom,(
% 3.49/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f18,plain,(
% 3.49/1.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.49/1.01    inference(ennf_transformation,[],[f2])).
% 3.49/1.01  
% 3.49/1.01  fof(f35,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f18])).
% 3.49/1.01  
% 3.49/1.01  fof(f9,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f23,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.49/1.01    inference(ennf_transformation,[],[f9])).
% 3.49/1.01  
% 3.49/1.01  fof(f48,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f23])).
% 3.49/1.01  
% 3.49/1.01  fof(f14,conjecture,(
% 3.49/1.01    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f15,negated_conjecture,(
% 3.49/1.01    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.49/1.01    inference(negated_conjecture,[],[f14])).
% 3.49/1.01  
% 3.49/1.01  fof(f25,plain,(
% 3.49/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.49/1.01    inference(ennf_transformation,[],[f15])).
% 3.49/1.01  
% 3.49/1.01  fof(f26,plain,(
% 3.49/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.49/1.01    inference(flattening,[],[f25])).
% 3.49/1.01  
% 3.49/1.01  fof(f32,plain,(
% 3.49/1.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f33,plain,(
% 3.49/1.01    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f32])).
% 3.49/1.01  
% 3.49/1.01  fof(f53,plain,(
% 3.49/1.01    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 3.49/1.01    inference(cnf_transformation,[],[f33])).
% 3.49/1.01  
% 3.49/1.01  fof(f5,axiom,(
% 3.49/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f41,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f5])).
% 3.49/1.01  
% 3.49/1.01  fof(f10,axiom,(
% 3.49/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f49,plain,(
% 3.49/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f10])).
% 3.49/1.01  
% 3.49/1.01  fof(f11,axiom,(
% 3.49/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f50,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f11])).
% 3.49/1.01  
% 3.49/1.01  fof(f12,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f51,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f12])).
% 3.49/1.01  
% 3.49/1.01  fof(f57,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f50,f51])).
% 3.49/1.01  
% 3.49/1.01  fof(f58,plain,(
% 3.49/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f49,f57])).
% 3.49/1.01  
% 3.49/1.01  fof(f64,plain,(
% 3.49/1.01    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5))),
% 3.49/1.01    inference(definition_unfolding,[],[f53,f41,f58])).
% 3.49/1.01  
% 3.49/1.01  fof(f13,axiom,(
% 3.49/1.01    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f24,plain,(
% 3.49/1.01    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.49/1.01    inference(ennf_transformation,[],[f13])).
% 3.49/1.01  
% 3.49/1.01  fof(f52,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f24])).
% 3.49/1.01  
% 3.49/1.01  fof(f63,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f52,f58])).
% 3.49/1.01  
% 3.49/1.01  fof(f3,axiom,(
% 3.49/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f16,plain,(
% 3.49/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.49/1.01    inference(rectify,[],[f3])).
% 3.49/1.01  
% 3.49/1.01  fof(f19,plain,(
% 3.49/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.49/1.01    inference(ennf_transformation,[],[f16])).
% 3.49/1.01  
% 3.49/1.01  fof(f27,plain,(
% 3.49/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f28,plain,(
% 3.49/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f27])).
% 3.49/1.01  
% 3.49/1.01  fof(f38,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f28])).
% 3.49/1.01  
% 3.49/1.01  fof(f54,plain,(
% 3.49/1.01    r2_hidden(sK5,sK4)),
% 3.49/1.01    inference(cnf_transformation,[],[f33])).
% 3.49/1.01  
% 3.49/1.01  fof(f55,plain,(
% 3.49/1.01    r1_xboole_0(sK4,sK3)),
% 3.49/1.01    inference(cnf_transformation,[],[f33])).
% 3.49/1.01  
% 3.49/1.01  fof(f1,axiom,(
% 3.49/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f34,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f1])).
% 3.49/1.01  
% 3.49/1.01  fof(f59,plain,(
% 3.49/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f34,f41,f41])).
% 3.49/1.01  
% 3.49/1.01  fof(f7,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f22,plain,(
% 3.49/1.01    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 3.49/1.01    inference(ennf_transformation,[],[f7])).
% 3.49/1.01  
% 3.49/1.01  fof(f45,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f22])).
% 3.49/1.01  
% 3.49/1.01  fof(f62,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f45,f41])).
% 3.49/1.01  
% 3.49/1.01  fof(f4,axiom,(
% 3.49/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f17,plain,(
% 3.49/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.49/1.01    inference(rectify,[],[f4])).
% 3.49/1.01  
% 3.49/1.01  fof(f20,plain,(
% 3.49/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.49/1.01    inference(ennf_transformation,[],[f17])).
% 3.49/1.01  
% 3.49/1.01  fof(f29,plain,(
% 3.49/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.49/1.01    introduced(choice_axiom,[])).
% 3.49/1.01  
% 3.49/1.01  fof(f30,plain,(
% 3.49/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f29])).
% 3.49/1.01  
% 3.49/1.01  fof(f40,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f30])).
% 3.49/1.01  
% 3.49/1.01  fof(f60,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.49/1.01    inference(definition_unfolding,[],[f40,f41])).
% 3.49/1.01  
% 3.49/1.01  fof(f39,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.49/1.01    inference(cnf_transformation,[],[f30])).
% 3.49/1.01  
% 3.49/1.01  fof(f61,plain,(
% 3.49/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 3.49/1.01    inference(definition_unfolding,[],[f39,f41])).
% 3.49/1.01  
% 3.49/1.01  fof(f6,axiom,(
% 3.49/1.01    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.01  
% 3.49/1.01  fof(f21,plain,(
% 3.49/1.01    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.49/1.01    inference(ennf_transformation,[],[f6])).
% 3.49/1.01  
% 3.49/1.01  fof(f42,plain,(
% 3.49/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.49/1.01    inference(cnf_transformation,[],[f21])).
% 3.49/1.01  
% 3.49/1.01  fof(f56,plain,(
% 3.49/1.01    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 3.49/1.01    inference(cnf_transformation,[],[f33])).
% 3.49/1.01  
% 3.49/1.01  cnf(c_405,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_404,plain,( X0 = X0 ),theory(equality) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2166,plain,
% 3.49/1.01      ( X0 != X1 | X1 = X0 ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_405,c_404]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_12,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.49/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3712,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,X1) | X0 = k4_xboole_0(X0,X1) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_2166,c_12]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_407,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.49/1.01      theory(equality) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2183,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_407,c_404]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4013,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.49/1.01      | r1_xboole_0(X0,X2)
% 3.49/1.01      | ~ r1_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_3712,c_2183]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.49/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_13,plain,
% 3.49/1.01      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_18,negated_conjecture,
% 3.49/1.01      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_240,plain,
% 3.49/1.01      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 3.49/1.01      | k2_enumset1(sK5,sK5,sK5,sK5) != X2
% 3.49/1.01      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X0 ),
% 3.49/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_241,plain,
% 3.49/1.01      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) ),
% 3.49/1.01      inference(unflattening,[status(thm)],[c_240]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_983,plain,
% 3.49/1.01      ( r1_xboole_0(k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_1,c_241]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4041,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.49/1.01      | r1_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_4013,c_983]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_14,plain,
% 3.49/1.01      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1313,plain,
% 3.49/1.01      ( r2_hidden(X0,X1) | r1_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_14,c_1]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4156,plain,
% 3.49/1.01      ( r2_hidden(sK5,X0)
% 3.49/1.01      | r1_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_4041,c_1313]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_2,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_4422,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,X1)
% 3.49/1.01      | ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 3.49/1.01      | r2_hidden(sK5,X1) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_4156,c_2]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_17,negated_conjecture,
% 3.49/1.01      ( r2_hidden(sK5,sK4) ),
% 3.49/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_16,negated_conjecture,
% 3.49/1.01      ( r1_xboole_0(sK4,sK3) ),
% 3.49/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1628,plain,
% 3.49/1.01      ( r2_hidden(X0,sK3) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1634,plain,
% 3.49/1.01      ( r2_hidden(sK5,sK3)
% 3.49/1.01      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_1628]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_992,plain,
% 3.49/1.01      ( ~ r2_hidden(sK5,X0)
% 3.49/1.01      | ~ r2_hidden(sK5,sK4)
% 3.49/1.01      | ~ r1_xboole_0(sK4,X0) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1670,plain,
% 3.49/1.01      ( ~ r2_hidden(sK5,sK3)
% 3.49/1.01      | ~ r2_hidden(sK5,sK4)
% 3.49/1.01      | ~ r1_xboole_0(sK4,sK3) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_992]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_0,plain,
% 3.49/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_10,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.49/1.01      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.49/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_821,plain,
% 3.49/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 3.49/1.01      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1989,plain,
% 3.49/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 3.49/1.01      | r1_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_0,c_821]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_814,plain,
% 3.49/1.01      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_819,plain,
% 3.49/1.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1090,plain,
% 3.49/1.01      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k2_enumset1(sK5,sK5,sK5,sK5))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_814,c_819]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.49/1.01      | ~ r1_xboole_0(X1,X2) ),
% 3.49/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_826,plain,
% 3.49/1.01      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.49/1.01      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.49/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3371,plain,
% 3.49/1.01      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.49/1.01      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_0,c_826]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_3659,plain,
% 3.49/1.01      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 3.49/1.01      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_1090,c_3371]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5631,plain,
% 3.49/1.01      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 3.49/1.01      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top ),
% 3.49/1.01      inference(superposition,[status(thm)],[c_1989,c_3659]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_5648,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 3.49/1.01      | ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
% 3.49/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_5631]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6996,plain,
% 3.49/1.01      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 3.49/1.01      inference(global_propositional_subsumption,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_4422,c_17,c_16,c_1634,c_1670,c_5648]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_6,plain,
% 3.49/1.01      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 3.49/1.01      | r1_xboole_0(X0,X1) ),
% 3.49/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_8415,plain,
% 3.49/1.01      ( r1_xboole_0(sK2,sK3) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_6996,c_6]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1339,plain,
% 3.49/1.01      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_9,plain,
% 3.49/1.01      ( ~ r1_xboole_0(X0,X1)
% 3.49/1.01      | ~ r1_xboole_0(X0,X2)
% 3.49/1.01      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.49/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_1054,plain,
% 3.49/1.01      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 3.49/1.01      | ~ r1_xboole_0(sK3,sK4)
% 3.49/1.01      | ~ r1_xboole_0(sK3,sK2) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_981,plain,
% 3.49/1.01      ( r1_xboole_0(sK3,sK4) ),
% 3.49/1.01      inference(resolution,[status(thm)],[c_1,c_16]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_945,plain,
% 3.49/1.01      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 3.49/1.01      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 3.49/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(c_15,negated_conjecture,
% 3.49/1.01      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 3.49/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.49/1.01  
% 3.49/1.01  cnf(contradiction,plain,
% 3.49/1.01      ( $false ),
% 3.49/1.01      inference(minisat,
% 3.49/1.01                [status(thm)],
% 3.49/1.01                [c_8415,c_1339,c_1054,c_981,c_945,c_15]) ).
% 3.49/1.01  
% 3.49/1.01  
% 3.49/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/1.01  
% 3.49/1.01  ------                               Statistics
% 3.49/1.01  
% 3.49/1.01  ------ Selected
% 3.49/1.01  
% 3.49/1.01  total_time:                             0.305
% 3.49/1.01  
%------------------------------------------------------------------------------

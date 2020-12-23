%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0432+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:17 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 150 expanded)
%              Number of clauses        :   22 (  28 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  216 ( 894 expanded)
%              Number of equality atoms :   38 ( 139 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f16,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).

fof(f27,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ~ ! [X0,X1] : k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f6,plain,(
    ? [X0,X1] : k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_relat_1(k2_xboole_0(X0,X1))
   => k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) != k1_relat_1(k2_xboole_0(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) != k1_relat_1(k2_xboole_0(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f6,f18])).

fof(f30,plain,(
    k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) != k1_relat_1(k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f26,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f22])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4574,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) != k1_relat_1(k2_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2576,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5)))
    | r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK5))
    | r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK4)) ),
    inference(resolution,[status(thm)],[c_2,c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1228,plain,
    ( r2_hidden(X0,k1_relat_1(k2_xboole_0(X1,X2)))
    | ~ r2_hidden(k4_tarski(X0,X3),X1) ),
    inference(resolution,[status(thm)],[c_8,c_4])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1638,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k2_xboole_0(X1,X2))) ),
    inference(resolution,[status(thm)],[c_1228,c_9])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1226,plain,
    ( r2_hidden(X0,k1_relat_1(k2_xboole_0(X1,X2)))
    | ~ r2_hidden(k4_tarski(X0,X3),X2) ),
    inference(resolution,[status(thm)],[c_8,c_3])).

cnf(c_1461,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k2_xboole_0(X2,X1))) ),
    inference(resolution,[status(thm)],[c_1226,c_9])).

cnf(c_2618,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2576,c_1638,c_1461])).

cnf(c_2421,plain,
    ( r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1266,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),k2_xboole_0(sK4,sK5))
    | r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),sK5)
    | r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_511,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5)))
    | r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_493,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5)))
    | ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK5))
    | k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) = k1_relat_1(k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_423,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5)))
    | ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK4))
    | k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) = k1_relat_1(k2_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4574,c_2618,c_2421,c_1266,c_511,c_493,c_423,c_10])).


%------------------------------------------------------------------------------

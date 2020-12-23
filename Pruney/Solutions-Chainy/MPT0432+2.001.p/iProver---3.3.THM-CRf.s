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
% DateTime   : Thu Dec  3 11:42:51 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.85/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/0.97  
% 2.85/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/0.97  
% 2.85/0.97  ------  iProver source info
% 2.85/0.97  
% 2.85/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.85/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/0.97  git: non_committed_changes: false
% 2.85/0.97  git: last_make_outside_of_git: false
% 2.85/0.97  
% 2.85/0.97  ------ 
% 2.85/0.97  ------ Parsing...
% 2.85/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.97  
% 2.85/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.97  ------ Proving...
% 2.85/0.97  ------ Problem Properties 
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  clauses                                 11
% 2.85/0.97  conjectures                             1
% 2.85/0.97  EPR                                     0
% 2.85/0.97  Horn                                    8
% 2.85/0.97  unary                                   1
% 2.85/0.97  binary                                  4
% 2.85/0.97  lits                                    28
% 2.85/0.97  lits eq                                 6
% 2.85/0.97  fd_pure                                 0
% 2.85/0.97  fd_pseudo                               0
% 2.85/0.97  fd_cond                                 0
% 2.85/0.97  fd_pseudo_cond                          5
% 2.85/0.97  AC symbols                              0
% 2.85/0.97  
% 2.85/0.97  ------ Input Options Time Limit: Unbounded
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  ------ 
% 2.85/0.97  Current options:
% 2.85/0.97  ------ 
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  ------ Proving...
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  % SZS status Theorem for theBenchmark.p
% 2.85/0.97  
% 2.85/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.97  
% 2.85/0.97  fof(f2,axiom,(
% 2.85/0.97    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f12,plain,(
% 2.85/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.85/0.97    inference(nnf_transformation,[],[f2])).
% 2.85/0.97  
% 2.85/0.97  fof(f13,plain,(
% 2.85/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.85/0.97    inference(rectify,[],[f12])).
% 2.85/0.97  
% 2.85/0.97  fof(f16,plain,(
% 2.85/0.97    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f15,plain,(
% 2.85/0.97    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0))) )),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f14,plain,(
% 2.85/0.97    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f17,plain,(
% 2.85/0.97    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.85/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).
% 2.85/0.97  
% 2.85/0.97  fof(f27,plain,(
% 2.85/0.97    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.85/0.97    inference(cnf_transformation,[],[f17])).
% 2.85/0.97  
% 2.85/0.97  fof(f34,plain,(
% 2.85/0.97    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.85/0.97    inference(equality_resolution,[],[f27])).
% 2.85/0.97  
% 2.85/0.97  fof(f1,axiom,(
% 2.85/0.97    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f7,plain,(
% 2.85/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.85/0.97    inference(nnf_transformation,[],[f1])).
% 2.85/0.97  
% 2.85/0.97  fof(f8,plain,(
% 2.85/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.85/0.97    inference(flattening,[],[f7])).
% 2.85/0.97  
% 2.85/0.97  fof(f9,plain,(
% 2.85/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.85/0.97    inference(rectify,[],[f8])).
% 2.85/0.97  
% 2.85/0.97  fof(f10,plain,(
% 2.85/0.97    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f11,plain,(
% 2.85/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.85/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 2.85/0.97  
% 2.85/0.97  fof(f23,plain,(
% 2.85/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.85/0.97    inference(cnf_transformation,[],[f11])).
% 2.85/0.97  
% 2.85/0.97  fof(f3,conjecture,(
% 2.85/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 2.85/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.97  
% 2.85/0.97  fof(f4,negated_conjecture,(
% 2.85/0.97    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 2.85/0.97    inference(negated_conjecture,[],[f3])).
% 2.85/0.97  
% 2.85/0.97  fof(f5,plain,(
% 2.85/0.97    ~! [X0,X1] : k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))),
% 2.85/0.97    inference(pure_predicate_removal,[],[f4])).
% 2.85/0.97  
% 2.85/0.97  fof(f6,plain,(
% 2.85/0.97    ? [X0,X1] : k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_relat_1(k2_xboole_0(X0,X1))),
% 2.85/0.97    inference(ennf_transformation,[],[f5])).
% 2.85/0.97  
% 2.85/0.97  fof(f18,plain,(
% 2.85/0.97    ? [X0,X1] : k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) != k1_relat_1(k2_xboole_0(X0,X1)) => k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) != k1_relat_1(k2_xboole_0(sK4,sK5))),
% 2.85/0.97    introduced(choice_axiom,[])).
% 2.85/0.97  
% 2.85/0.97  fof(f19,plain,(
% 2.85/0.97    k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) != k1_relat_1(k2_xboole_0(sK4,sK5))),
% 2.85/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f6,f18])).
% 2.85/0.97  
% 2.85/0.97  fof(f30,plain,(
% 2.85/0.97    k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) != k1_relat_1(k2_xboole_0(sK4,sK5))),
% 2.85/0.97    inference(cnf_transformation,[],[f19])).
% 2.85/0.97  
% 2.85/0.97  fof(f21,plain,(
% 2.85/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.85/0.97    inference(cnf_transformation,[],[f11])).
% 2.85/0.97  
% 2.85/0.97  fof(f32,plain,(
% 2.85/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 2.85/0.97    inference(equality_resolution,[],[f21])).
% 2.85/0.97  
% 2.85/0.97  fof(f26,plain,(
% 2.85/0.97    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.85/0.97    inference(cnf_transformation,[],[f17])).
% 2.85/0.97  
% 2.85/0.97  fof(f35,plain,(
% 2.85/0.97    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.85/0.97    inference(equality_resolution,[],[f26])).
% 2.85/0.97  
% 2.85/0.97  fof(f22,plain,(
% 2.85/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.85/0.97    inference(cnf_transformation,[],[f11])).
% 2.85/0.97  
% 2.85/0.97  fof(f31,plain,(
% 2.85/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.85/0.97    inference(equality_resolution,[],[f22])).
% 2.85/0.97  
% 2.85/0.97  fof(f20,plain,(
% 2.85/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.85/0.97    inference(cnf_transformation,[],[f11])).
% 2.85/0.97  
% 2.85/0.97  fof(f33,plain,(
% 2.85/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 2.85/0.97    inference(equality_resolution,[],[f20])).
% 2.85/0.97  
% 2.85/0.97  fof(f25,plain,(
% 2.85/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.85/0.97    inference(cnf_transformation,[],[f11])).
% 2.85/0.97  
% 2.85/0.97  fof(f24,plain,(
% 2.85/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.85/0.97    inference(cnf_transformation,[],[f11])).
% 2.85/0.97  
% 2.85/0.97  cnf(c_8,plain,
% 2.85/0.97      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 2.85/0.97      inference(cnf_transformation,[],[f34]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_4574,plain,
% 2.85/0.97      ( r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK5))
% 2.85/0.97      | ~ r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),sK5) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2,plain,
% 2.85/0.97      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.85/0.97      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.85/0.97      | r2_hidden(sK0(X0,X1,X2),X0)
% 2.85/0.97      | k2_xboole_0(X0,X1) = X2 ),
% 2.85/0.97      inference(cnf_transformation,[],[f23]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_10,negated_conjecture,
% 2.85/0.97      ( k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) != k1_relat_1(k2_xboole_0(sK4,sK5)) ),
% 2.85/0.97      inference(cnf_transformation,[],[f30]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2576,plain,
% 2.85/0.97      ( r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5)))
% 2.85/0.97      | r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK5))
% 2.85/0.97      | r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK4)) ),
% 2.85/0.97      inference(resolution,[status(thm)],[c_2,c_10]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_4,plain,
% 2.85/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 2.85/0.97      inference(cnf_transformation,[],[f32]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1228,plain,
% 2.85/0.97      ( r2_hidden(X0,k1_relat_1(k2_xboole_0(X1,X2)))
% 2.85/0.97      | ~ r2_hidden(k4_tarski(X0,X3),X1) ),
% 2.85/0.97      inference(resolution,[status(thm)],[c_8,c_4]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_9,plain,
% 2.85/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.97      | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
% 2.85/0.97      inference(cnf_transformation,[],[f35]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1638,plain,
% 2.85/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.97      | r2_hidden(X0,k1_relat_1(k2_xboole_0(X1,X2))) ),
% 2.85/0.97      inference(resolution,[status(thm)],[c_1228,c_9]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_3,plain,
% 2.85/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 2.85/0.97      inference(cnf_transformation,[],[f31]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1226,plain,
% 2.85/0.97      ( r2_hidden(X0,k1_relat_1(k2_xboole_0(X1,X2)))
% 2.85/0.97      | ~ r2_hidden(k4_tarski(X0,X3),X2) ),
% 2.85/0.97      inference(resolution,[status(thm)],[c_8,c_3]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1461,plain,
% 2.85/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.97      | r2_hidden(X0,k1_relat_1(k2_xboole_0(X2,X1))) ),
% 2.85/0.97      inference(resolution,[status(thm)],[c_1226,c_9]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2618,plain,
% 2.85/0.97      ( r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5))) ),
% 2.85/0.97      inference(forward_subsumption_resolution,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_2576,c_1638,c_1461]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_2421,plain,
% 2.85/0.97      ( r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK4))
% 2.85/0.97      | ~ r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),sK4) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_5,plain,
% 2.85/0.97      ( r2_hidden(X0,X1)
% 2.85/0.97      | r2_hidden(X0,X2)
% 2.85/0.97      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 2.85/0.97      inference(cnf_transformation,[],[f33]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1266,plain,
% 2.85/0.97      ( ~ r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),k2_xboole_0(sK4,sK5))
% 2.85/0.97      | r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),sK5)
% 2.85/0.97      | r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),sK4) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_511,plain,
% 2.85/0.97      ( ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5)))
% 2.85/0.97      | r2_hidden(k4_tarski(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),sK3(k2_xboole_0(sK4,sK5),sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))))),k2_xboole_0(sK4,sK5)) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_0,plain,
% 2.85/0.97      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.85/0.97      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.85/0.97      | k2_xboole_0(X0,X1) = X2 ),
% 2.85/0.97      inference(cnf_transformation,[],[f25]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_493,plain,
% 2.85/0.97      ( ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5)))
% 2.85/0.97      | ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK5))
% 2.85/0.97      | k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) = k1_relat_1(k2_xboole_0(sK4,sK5)) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_1,plain,
% 2.85/0.97      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.85/0.97      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.85/0.97      | k2_xboole_0(X0,X1) = X2 ),
% 2.85/0.97      inference(cnf_transformation,[],[f24]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(c_423,plain,
% 2.85/0.97      ( ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(k2_xboole_0(sK4,sK5)))
% 2.85/0.97      | ~ r2_hidden(sK0(k1_relat_1(sK4),k1_relat_1(sK5),k1_relat_1(k2_xboole_0(sK4,sK5))),k1_relat_1(sK4))
% 2.85/0.97      | k2_xboole_0(k1_relat_1(sK4),k1_relat_1(sK5)) = k1_relat_1(k2_xboole_0(sK4,sK5)) ),
% 2.85/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 2.85/0.97  
% 2.85/0.97  cnf(contradiction,plain,
% 2.85/0.97      ( $false ),
% 2.85/0.97      inference(minisat,
% 2.85/0.97                [status(thm)],
% 2.85/0.97                [c_4574,c_2618,c_2421,c_1266,c_511,c_493,c_423,c_10]) ).
% 2.85/0.97  
% 2.85/0.97  
% 2.85/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/0.97  
% 2.85/0.97  ------                               Statistics
% 2.85/0.97  
% 2.85/0.97  ------ Selected
% 2.85/0.97  
% 2.85/0.97  total_time:                             0.166
% 2.85/0.97  
%------------------------------------------------------------------------------

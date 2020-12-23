%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:38 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 164 expanded)
%              Number of clauses        :   29 (  38 expanded)
%              Number of leaves         :    6 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  264 (1186 expanded)
%              Number of equality atoms :   40 ( 170 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(flattening,[],[f6])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f7])).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k4_xboole_0(k4_xboole_0(X0,X1),X2)
   => k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).

fof(f30,plain,(
    k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_683,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X1)
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1881,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,X0))
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_3075,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4)
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_673,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1760,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_767,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_8,c_12])).

cnf(c_1011,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_10,c_767])).

cnf(c_1507,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(resolution,[status(thm)],[c_1011,c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1513,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1507,c_4])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_605,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,X0))
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1289,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3)
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_1286,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1000,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(resolution,[status(thm)],[c_11,c_767])).

cnf(c_530,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1208,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_530])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_694,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4)
    | k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_490,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_487,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
    | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4)
    | k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3075,c_1760,c_1513,c_1289,c_1286,c_1208,c_694,c_490,c_487,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.85/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.98  
% 3.85/0.98  ------  iProver source info
% 3.85/0.98  
% 3.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.98  git: non_committed_changes: false
% 3.85/0.98  git: last_make_outside_of_git: false
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  ------ Parsing...
% 3.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 13
% 3.85/0.98  conjectures                             1
% 3.85/0.98  EPR                                     0
% 3.85/0.98  Horn                                    7
% 3.85/0.98  unary                                   1
% 3.85/0.98  binary                                  4
% 3.85/0.98  lits                                    35
% 3.85/0.98  lits eq                                 7
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 0
% 3.85/0.98  fd_pseudo_cond                          6
% 3.85/0.98  AC symbols                              0
% 3.85/0.98  
% 3.85/0.98  ------ Input Options Time Limit: Unbounded
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  Current options:
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS status Theorem for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  fof(f1,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f6,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.85/0.98    inference(nnf_transformation,[],[f1])).
% 3.85/0.98  
% 3.85/0.98  fof(f7,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.85/0.98    inference(flattening,[],[f6])).
% 3.85/0.98  
% 3.85/0.98  fof(f8,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.85/0.98    inference(rectify,[],[f7])).
% 3.85/0.98  
% 3.85/0.98  fof(f9,plain,(
% 3.85/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f10,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 3.85/0.98  
% 3.85/0.98  fof(f18,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.85/0.98    inference(cnf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f33,plain,(
% 3.85/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.85/0.98    inference(equality_resolution,[],[f18])).
% 3.85/0.98  
% 3.85/0.98  fof(f20,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.85/0.98    inference(cnf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f31,plain,(
% 3.85/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.85/0.98    inference(equality_resolution,[],[f20])).
% 3.85/0.98  
% 3.85/0.98  fof(f2,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f11,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.98    inference(nnf_transformation,[],[f2])).
% 3.85/0.98  
% 3.85/0.98  fof(f12,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.98    inference(flattening,[],[f11])).
% 3.85/0.98  
% 3.85/0.98  fof(f13,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.98    inference(rectify,[],[f12])).
% 3.85/0.98  
% 3.85/0.98  fof(f14,plain,(
% 3.85/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f15,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 3.85/0.98  
% 3.85/0.98  fof(f25,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f35,plain,(
% 3.85/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.85/0.98    inference(equality_resolution,[],[f25])).
% 3.85/0.98  
% 3.85/0.98  fof(f27,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f3,conjecture,(
% 3.85/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f4,negated_conjecture,(
% 3.85/0.98    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.85/0.98    inference(negated_conjecture,[],[f3])).
% 3.85/0.98  
% 3.85/0.98  fof(f5,plain,(
% 3.85/0.98    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.85/0.98    inference(ennf_transformation,[],[f4])).
% 3.85/0.98  
% 3.85/0.98  fof(f16,plain,(
% 3.85/0.98    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k4_xboole_0(k4_xboole_0(X0,X1),X2) => k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f17,plain,(
% 3.85/0.98    k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).
% 3.85/0.98  
% 3.85/0.98  fof(f30,plain,(
% 3.85/0.98    k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 3.85/0.98    inference(cnf_transformation,[],[f17])).
% 3.85/0.98  
% 3.85/0.98  fof(f19,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.85/0.98    inference(cnf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f32,plain,(
% 3.85/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.85/0.98    inference(equality_resolution,[],[f19])).
% 3.85/0.98  
% 3.85/0.98  fof(f26,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f34,plain,(
% 3.85/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.85/0.98    inference(equality_resolution,[],[f26])).
% 3.85/0.98  
% 3.85/0.98  fof(f24,plain,(
% 3.85/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f36,plain,(
% 3.85/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.85/0.98    inference(equality_resolution,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f28,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f29,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5,plain,
% 3.85/0.98      ( r2_hidden(X0,X1)
% 3.85/0.98      | r2_hidden(X0,X2)
% 3.85/0.98      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_683,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X1)
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(X1,X0)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1881,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,X0))
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_683]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3075,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4)
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_1881]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3,plain,
% 3.85/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_673,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(X1,X0)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1760,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_673]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_10,plain,
% 3.85/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_8,plain,
% 3.85/0.98      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.85/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.85/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.85/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_12,negated_conjecture,
% 3.85/0.98      ( k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_767,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3)) ),
% 3.85/0.98      inference(resolution,[status(thm)],[c_8,c_12]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1011,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
% 3.85/0.98      inference(resolution,[status(thm)],[c_10,c_767]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1507,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.85/0.98      inference(resolution,[status(thm)],[c_1011,c_10]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4,plain,
% 3.85/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1513,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3) ),
% 3.85/0.98      inference(forward_subsumption_resolution,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_1507,c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9,plain,
% 3.85/0.98      ( ~ r2_hidden(X0,X1)
% 3.85/0.98      | r2_hidden(X0,X2)
% 3.85/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_605,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),X0)
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,X0))
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1289,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK3)
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_605]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1286,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4))
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_605]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11,plain,
% 3.85/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1000,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.85/0.98      inference(resolution,[status(thm)],[c_11,c_767]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_530,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1208,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK2) ),
% 3.85/0.98      inference(global_propositional_subsumption,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_1000,c_530]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 3.85/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.85/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.85/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_694,plain,
% 3.85/0.98      ( r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4)
% 3.85/0.98      | k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_490,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k2_xboole_0(sK3,sK4)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.85/0.98      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.85/0.98      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.85/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.85/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_487,plain,
% 3.85/0.98      ( ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 3.85/0.98      | ~ r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),k4_xboole_0(sK2,sK3))
% 3.85/0.98      | r2_hidden(sK1(k4_xboole_0(sK2,sK3),sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))),sK4)
% 3.85/0.98      | k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(contradiction,plain,
% 3.85/0.98      ( $false ),
% 3.85/0.98      inference(minisat,
% 3.85/0.98                [status(thm)],
% 3.85/0.98                [c_3075,c_1760,c_1513,c_1289,c_1286,c_1208,c_694,c_490,
% 3.85/0.98                 c_487,c_12]) ).
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  ------                               Statistics
% 3.85/0.98  
% 3.85/0.98  ------ Selected
% 3.85/0.98  
% 3.85/0.98  total_time:                             0.133
% 3.85/0.98  
%------------------------------------------------------------------------------

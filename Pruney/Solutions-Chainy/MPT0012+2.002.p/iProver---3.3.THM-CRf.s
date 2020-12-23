%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:13 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 496 expanded)
%              Number of clauses        :   32 ( 109 expanded)
%              Number of leaves         :    4 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          :  188 (3592 expanded)
%              Number of equality atoms :   32 ( 535 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
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

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f15])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
   => k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f11])).

fof(f20,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f14,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1970,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(X0,X1),X2,X3),X1)
    | ~ r2_hidden(sK0(k2_xboole_0(X0,X1),X2,X3),X3)
    | k2_xboole_0(k2_xboole_0(X0,X1),X2) = X3 ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_707,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3) ),
    inference(resolution,[status(thm)],[c_2,c_7])).

cnf(c_7124,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2)
    | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_1970,c_707])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_922,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3) ),
    inference(resolution,[status(thm)],[c_5,c_707])).

cnf(c_931,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_922,c_3])).

cnf(c_1159,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
    inference(resolution,[status(thm)],[c_931,c_5])).

cnf(c_342,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_448,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,X0))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_455,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_1469,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1159,c_342,c_455])).

cnf(c_1476,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1469,c_3])).

cnf(c_1487,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1) ),
    inference(resolution,[status(thm)],[c_1476,c_5])).

cnf(c_1974,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(X0,X1),X2,X3),X0)
    | ~ r2_hidden(sK0(k2_xboole_0(X0,X1),X2,X3),X3)
    | k2_xboole_0(k2_xboole_0(X0,X1),X2) = X3 ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_7182,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1)
    | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_1974,c_707])).

cnf(c_8775,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7124,c_7,c_1487,c_7182])).

cnf(c_8791,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
    | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_8775,c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_283,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
    | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9349,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8791,c_7,c_283])).

cnf(c_9362,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_9349,c_3])).

cnf(c_991,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(X0,sK3),X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2371,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),X0))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_5370,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_4514,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,X0))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4521,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_4514])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9362,c_9349,c_5370,c_4521,c_1476])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:51:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.47/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/0.98  
% 3.47/0.98  ------  iProver source info
% 3.47/0.98  
% 3.47/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.47/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/0.98  git: non_committed_changes: false
% 3.47/0.98  git: last_make_outside_of_git: false
% 3.47/0.98  
% 3.47/0.98  ------ 
% 3.47/0.98  ------ Parsing...
% 3.47/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/0.98  
% 3.47/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/0.98  ------ Proving...
% 3.47/0.98  ------ Problem Properties 
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  clauses                                 8
% 3.47/0.98  conjectures                             1
% 3.47/0.98  EPR                                     0
% 3.47/0.98  Horn                                    6
% 3.47/0.98  unary                                   2
% 3.47/0.98  binary                                  2
% 3.47/0.98  lits                                    19
% 3.47/0.98  lits eq                                 5
% 3.47/0.98  fd_pure                                 0
% 3.47/0.98  fd_pseudo                               0
% 3.47/0.98  fd_cond                                 0
% 3.47/0.98  fd_pseudo_cond                          3
% 3.47/0.98  AC symbols                              0
% 3.47/0.98  
% 3.47/0.98  ------ Input Options Time Limit: Unbounded
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ 
% 3.47/0.98  Current options:
% 3.47/0.98  ------ 
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  ------ Proving...
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  % SZS status Theorem for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  fof(f1,axiom,(
% 3.47/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f6,plain,(
% 3.47/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.47/0.98    inference(nnf_transformation,[],[f1])).
% 3.47/0.98  
% 3.47/0.98  fof(f7,plain,(
% 3.47/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.47/0.98    inference(flattening,[],[f6])).
% 3.47/0.98  
% 3.47/0.98  fof(f8,plain,(
% 3.47/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.47/0.98    inference(rectify,[],[f7])).
% 3.47/0.98  
% 3.47/0.98  fof(f9,plain,(
% 3.47/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.47/0.98    introduced(choice_axiom,[])).
% 3.47/0.98  
% 3.47/0.98  fof(f10,plain,(
% 3.47/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.47/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 3.47/0.98  
% 3.47/0.98  fof(f17,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f10])).
% 3.47/0.98  
% 3.47/0.98  fof(f15,plain,(
% 3.47/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.47/0.98    inference(cnf_transformation,[],[f10])).
% 3.47/0.98  
% 3.47/0.98  fof(f21,plain,(
% 3.47/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.47/0.98    inference(equality_resolution,[],[f15])).
% 3.47/0.98  
% 3.47/0.98  fof(f16,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f10])).
% 3.47/0.98  
% 3.47/0.98  fof(f3,conjecture,(
% 3.47/0.98    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 3.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/0.98  
% 3.47/0.98  fof(f4,negated_conjecture,(
% 3.47/0.98    ~! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 3.47/0.98    inference(negated_conjecture,[],[f3])).
% 3.47/0.98  
% 3.47/0.98  fof(f5,plain,(
% 3.47/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 3.47/0.98    inference(ennf_transformation,[],[f4])).
% 3.47/0.98  
% 3.47/0.98  fof(f11,plain,(
% 3.47/0.98    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) => k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),
% 3.47/0.98    introduced(choice_axiom,[])).
% 3.47/0.98  
% 3.47/0.98  fof(f12,plain,(
% 3.47/0.98    k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),
% 3.47/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f11])).
% 3.47/0.98  
% 3.47/0.98  fof(f20,plain,(
% 3.47/0.98    k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),
% 3.47/0.98    inference(cnf_transformation,[],[f12])).
% 3.47/0.98  
% 3.47/0.98  fof(f13,plain,(
% 3.47/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.47/0.98    inference(cnf_transformation,[],[f10])).
% 3.47/0.98  
% 3.47/0.98  fof(f23,plain,(
% 3.47/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.47/0.98    inference(equality_resolution,[],[f13])).
% 3.47/0.98  
% 3.47/0.98  fof(f14,plain,(
% 3.47/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.47/0.98    inference(cnf_transformation,[],[f10])).
% 3.47/0.98  
% 3.47/0.98  fof(f22,plain,(
% 3.47/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.47/0.98    inference(equality_resolution,[],[f14])).
% 3.47/0.98  
% 3.47/0.98  fof(f18,plain,(
% 3.47/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.47/0.98    inference(cnf_transformation,[],[f10])).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.47/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.47/0.98      | k2_xboole_0(X0,X1) = X2 ),
% 3.47/0.98      inference(cnf_transformation,[],[f17]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_3,plain,
% 3.47/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.47/0.98      inference(cnf_transformation,[],[f21]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1970,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(k2_xboole_0(X0,X1),X2,X3),X1)
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(X0,X1),X2,X3),X3)
% 3.47/0.98      | k2_xboole_0(k2_xboole_0(X0,X1),X2) = X3 ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_2,plain,
% 3.47/0.98      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.47/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.47/0.98      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.47/0.98      | k2_xboole_0(X0,X1) = X2 ),
% 3.47/0.98      inference(cnf_transformation,[],[f16]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_7,negated_conjecture,
% 3.47/0.98      ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
% 3.47/0.98      inference(cnf_transformation,[],[f20]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_707,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3) ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_2,c_7]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_7124,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2)
% 3.47/0.98      | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_1970,c_707]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_5,plain,
% 3.47/0.98      ( r2_hidden(X0,X1)
% 3.47/0.98      | r2_hidden(X0,X2)
% 3.47/0.98      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.47/0.98      inference(cnf_transformation,[],[f23]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_922,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3) ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_5,c_707]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_931,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2)) ),
% 3.47/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_922,c_3]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1159,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_931,c_5]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_342,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2)
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_4,plain,
% 3.47/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.47/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_448,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,X0))
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_455,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_448]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1469,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
% 3.47/0.98      inference(global_propositional_subsumption,
% 3.47/0.98                [status(thm)],
% 3.47/0.98                [c_1159,c_342,c_455]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1476,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
% 3.47/0.98      inference(forward_subsumption_resolution,
% 3.47/0.98                [status(thm)],
% 3.47/0.98                [c_1469,c_3]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1487,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2)
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1) ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_1476,c_5]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_1974,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(k2_xboole_0(X0,X1),X2,X3),X0)
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(X0,X1),X2,X3),X3)
% 3.47/0.98      | k2_xboole_0(k2_xboole_0(X0,X1),X2) = X3 ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_7182,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK1)
% 3.47/0.98      | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_1974,c_707]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_8775,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3) ),
% 3.47/0.98      inference(global_propositional_subsumption,
% 3.47/0.98                [status(thm)],
% 3.47/0.98                [c_7124,c_7,c_1487,c_7182]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_8791,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
% 3.47/0.98      | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_8775,c_1]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_0,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.47/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.47/0.98      | k2_xboole_0(X0,X1) = X2 ),
% 3.47/0.98      inference(cnf_transformation,[],[f18]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_283,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)))
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK3)
% 3.47/0.98      | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_9349,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))) ),
% 3.47/0.98      inference(global_propositional_subsumption,
% 3.47/0.98                [status(thm)],
% 3.47/0.98                [c_8791,c_7,c_283]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_9362,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3)) ),
% 3.47/0.98      inference(resolution,[status(thm)],[c_9349,c_3]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_991,plain,
% 3.47/0.98      ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,sK3))
% 3.47/0.98      | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(X0,sK3),X1)) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_2371,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),X0))
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3)) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_991]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_5370,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3)))
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK3)) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_2371]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_4514,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,X0))
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(c_4521,plain,
% 3.47/0.98      ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
% 3.47/0.98      | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(k2_xboole_0(sK1,sK3),k2_xboole_0(sK2,sK3))),sK2) ),
% 3.47/0.98      inference(instantiation,[status(thm)],[c_4514]) ).
% 3.47/0.98  
% 3.47/0.98  cnf(contradiction,plain,
% 3.47/0.98      ( $false ),
% 3.47/0.98      inference(minisat,
% 3.47/0.98                [status(thm)],
% 3.47/0.98                [c_9362,c_9349,c_5370,c_4521,c_1476]) ).
% 3.47/0.98  
% 3.47/0.98  
% 3.47/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/0.98  
% 3.47/0.98  ------                               Statistics
% 3.47/0.98  
% 3.47/0.98  ------ Selected
% 3.47/0.98  
% 3.47/0.98  total_time:                             0.297
% 3.47/0.98  
%------------------------------------------------------------------------------

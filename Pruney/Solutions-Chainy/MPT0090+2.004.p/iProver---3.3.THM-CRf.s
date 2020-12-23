%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:38 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 203 expanded)
%              Number of clauses        :   64 (  96 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  302 (1014 expanded)
%              Number of equality atoms :  126 ( 285 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( k4_xboole_0(sK1,sK2) != sK1
        | ~ r1_xboole_0(sK1,sK2) )
      & ( k4_xboole_0(sK1,sK2) = sK1
        | r1_xboole_0(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( k4_xboole_0(sK1,sK2) != sK1
      | ~ r1_xboole_0(sK1,sK2) )
    & ( k4_xboole_0(sK1,sK2) = sK1
      | r1_xboole_0(sK1,sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f21])).

fof(f36,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f37,plain,
    ( k4_xboole_0(sK1,sK2) != sK1
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_178,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3164,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(X2,X3,X4),X5)
    | X1 != X5
    | X0 != sK0(X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_7413,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,X0),X1)
    | r2_hidden(sK0(sK1,sK2,X0),X2)
    | X2 != X1
    | sK0(sK1,sK2,X0) != sK0(sK1,sK2,X0) ),
    inference(instantiation,[status(thm)],[c_3164])).

cnf(c_17571,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,X0),X1)
    | r2_hidden(sK0(sK1,sK2,X0),k4_xboole_0(X2,sK1))
    | sK0(sK1,sK2,X0) != sK0(sK1,sK2,X0)
    | k4_xboole_0(X2,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_7413])).

cnf(c_28794,plain,
    ( r2_hidden(sK0(sK1,sK2,X0),k4_xboole_0(X1,sK1))
    | ~ r2_hidden(sK0(sK1,sK2,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | sK0(sK1,sK2,X0) != sK0(sK1,sK2,X0)
    | k4_xboole_0(X1,sK1) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_17571])).

cnf(c_28797,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,sK1))
    | sK0(sK1,sK2,sK1) != sK0(sK1,sK2,sK1)
    | k4_xboole_0(sK1,sK1) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_28794])).

cnf(c_176,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1903,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X3) != X1
    | k4_xboole_0(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_4067,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | k4_xboole_0(X3,X4) = X0
    | k4_xboole_0(X3,X4) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_15666,plain,
    ( k4_xboole_0(X0,X1) != k4_xboole_0(X2,X3)
    | k4_xboole_0(X0,X1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_4067])).

cnf(c_15672,plain,
    ( k4_xboole_0(sK1,sK1) != k4_xboole_0(sK1,sK1)
    | k4_xboole_0(sK1,sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_15666])).

cnf(c_175,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_863,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_176,c_175])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2735,plain,
    ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_863,c_10])).

cnf(c_3389,plain,
    ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_2735,c_176])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1001,plain,
    ( r2_hidden(sK0(X0,X1,X0),X0)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(factoring,[status(thm)],[c_3])).

cnf(c_2886,plain,
    ( r2_hidden(sK0(X0,X1,X0),X0)
    | X0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_1001,c_863])).

cnf(c_5906,plain,
    ( r2_hidden(sK0(X0,k4_xboole_0(X0,k1_xboole_0),X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_3389,c_2886])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5925,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(X0,X1)),X0)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_5906,c_6])).

cnf(c_5927,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k1_xboole_0),k4_xboole_0(sK1,sK1)),sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5925])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5921,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(X0,X1)),X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_5906,c_5])).

cnf(c_5923,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k1_xboole_0),k4_xboole_0(sK1,sK1)),sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5921])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1450,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK1),X0)
    | r2_hidden(sK0(sK1,sK2,sK1),X1)
    | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3292,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK1),X0)
    | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X0,k4_xboole_0(X1,sK2)))
    | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_3294,plain,
    ( r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(sK1,sK2,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_3292])).

cnf(c_1291,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_1911,plain,
    ( X0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | X0 != k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_3011,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k4_xboole_0(X0,X1) != k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_3012,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0
    | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k4_xboole_0(sK1,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3011])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_861,plain,
    ( r1_xboole_0(sK1,sK2)
    | X0 != sK1
    | k4_xboole_0(sK1,sK2) = X0 ),
    inference(resolution,[status(thm)],[c_176,c_13])).

cnf(c_1830,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(sK1,sK2))
    | X2 != X0
    | X1 != sK1 ),
    inference(resolution,[status(thm)],[c_178,c_861])).

cnf(c_184,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_943,plain,
    ( k4_xboole_0(sK1,sK2) != X0
    | sK1 != X0
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_944,plain,
    ( k4_xboole_0(sK1,sK2) != sK1
    | sK1 = k4_xboole_0(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_1031,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_179,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_591,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X3)
    | X1 != X3
    | X0 != k4_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_666,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | r1_xboole_0(sK1,sK2)
    | sK2 != X1
    | sK1 != k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_1368,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,sK2),sK2)
    | r1_xboole_0(sK1,sK2)
    | sK2 != sK2
    | sK1 != k4_xboole_0(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1371,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | r1_xboole_0(sK1,sK2)
    | sK2 != sK2
    | sK1 != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_11,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2332,plain,
    ( r1_xboole_0(k4_xboole_0(X0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2334,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_2553,plain,
    ( r1_xboole_0(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1830,c_13,c_184,c_944,c_1031,c_1371,c_2334])).

cnf(c_1470,plain,
    ( sK0(sK1,sK2,sK1) = sK0(sK1,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_929,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X0,sK2))
    | ~ r2_hidden(sK0(sK1,sK2,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_931,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(sK1,sK2,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_905,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X0,sK1))
    | ~ r2_hidden(sK0(sK1,sK2,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_907,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,sK1))
    | ~ r2_hidden(sK0(sK1,sK2,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_900,plain,
    ( r2_hidden(sK0(sK1,sK2,sK1),sK2)
    | ~ r2_hidden(sK0(sK1,sK2,sK1),sK1)
    | k4_xboole_0(sK1,sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_738,plain,
    ( r2_hidden(sK0(sK1,sK2,sK1),sK1)
    | k4_xboole_0(sK1,sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_708,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_177,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_180,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_12,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28797,c_15672,c_5927,c_5923,c_3294,c_3012,c_2553,c_1470,c_931,c_907,c_900,c_738,c_708,c_184,c_180,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:48:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  % Running in FOF mode
% 7.72/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/1.51  
% 7.72/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.72/1.51  
% 7.72/1.51  ------  iProver source info
% 7.72/1.51  
% 7.72/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.72/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.72/1.51  git: non_committed_changes: false
% 7.72/1.51  git: last_make_outside_of_git: false
% 7.72/1.51  
% 7.72/1.51  ------ 
% 7.72/1.51  ------ Parsing...
% 7.72/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.72/1.51  
% 7.72/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.72/1.51  
% 7.72/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.72/1.51  
% 7.72/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.51  ------ Proving...
% 7.72/1.51  ------ Problem Properties 
% 7.72/1.51  
% 7.72/1.51  
% 7.72/1.51  clauses                                 14
% 7.72/1.51  conjectures                             2
% 7.72/1.51  EPR                                     1
% 7.72/1.51  Horn                                    9
% 7.72/1.51  unary                                   3
% 7.72/1.51  binary                                  7
% 7.72/1.51  lits                                    30
% 7.72/1.51  lits eq                                 9
% 7.72/1.51  fd_pure                                 0
% 7.72/1.51  fd_pseudo                               0
% 7.72/1.51  fd_cond                                 0
% 7.72/1.51  fd_pseudo_cond                          3
% 7.72/1.51  AC symbols                              0
% 7.72/1.51  
% 7.72/1.51  ------ Input Options Time Limit: Unbounded
% 7.72/1.51  
% 7.72/1.51  
% 7.72/1.51  ------ 
% 7.72/1.51  Current options:
% 7.72/1.51  ------ 
% 7.72/1.51  
% 7.72/1.51  
% 7.72/1.51  
% 7.72/1.51  
% 7.72/1.51  ------ Proving...
% 7.72/1.51  
% 7.72/1.51  
% 7.72/1.51  % SZS status Theorem for theBenchmark.p
% 7.72/1.51  
% 7.72/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.72/1.51  
% 7.72/1.51  fof(f5,axiom,(
% 7.72/1.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.72/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.51  
% 7.72/1.51  fof(f33,plain,(
% 7.72/1.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.72/1.51    inference(cnf_transformation,[],[f5])).
% 7.72/1.51  
% 7.72/1.51  fof(f7,axiom,(
% 7.72/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.72/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.51  
% 7.72/1.51  fof(f34,plain,(
% 7.72/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.72/1.51    inference(cnf_transformation,[],[f7])).
% 7.72/1.51  
% 7.72/1.51  fof(f41,plain,(
% 7.72/1.51    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.72/1.51    inference(definition_unfolding,[],[f33,f34])).
% 7.72/1.51  
% 7.72/1.51  fof(f2,axiom,(
% 7.72/1.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.72/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.51  
% 7.72/1.51  fof(f14,plain,(
% 7.72/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.72/1.51    inference(nnf_transformation,[],[f2])).
% 7.72/1.51  
% 7.72/1.51  fof(f15,plain,(
% 7.72/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.72/1.51    inference(flattening,[],[f14])).
% 7.72/1.51  
% 7.72/1.51  fof(f16,plain,(
% 7.72/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.72/1.51    inference(rectify,[],[f15])).
% 7.72/1.51  
% 7.72/1.51  fof(f17,plain,(
% 7.72/1.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.72/1.51    introduced(choice_axiom,[])).
% 7.72/1.51  
% 7.72/1.51  fof(f18,plain,(
% 7.72/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.72/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 7.72/1.51  
% 7.72/1.51  fof(f27,plain,(
% 7.72/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.72/1.51    inference(cnf_transformation,[],[f18])).
% 7.72/1.51  
% 7.72/1.51  fof(f24,plain,(
% 7.72/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.72/1.51    inference(cnf_transformation,[],[f18])).
% 7.72/1.51  
% 7.72/1.51  fof(f44,plain,(
% 7.72/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.72/1.51    inference(equality_resolution,[],[f24])).
% 7.72/1.51  
% 7.72/1.51  fof(f25,plain,(
% 7.72/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.72/1.51    inference(cnf_transformation,[],[f18])).
% 7.72/1.51  
% 7.72/1.51  fof(f43,plain,(
% 7.72/1.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.72/1.51    inference(equality_resolution,[],[f25])).
% 7.72/1.51  
% 7.72/1.51  fof(f26,plain,(
% 7.72/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.72/1.51    inference(cnf_transformation,[],[f18])).
% 7.72/1.51  
% 7.72/1.51  fof(f42,plain,(
% 7.72/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.72/1.51    inference(equality_resolution,[],[f26])).
% 7.72/1.51  
% 7.72/1.51  fof(f9,conjecture,(
% 7.72/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.72/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.51  
% 7.72/1.51  fof(f10,negated_conjecture,(
% 7.72/1.51    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.72/1.51    inference(negated_conjecture,[],[f9])).
% 7.72/1.51  
% 7.72/1.51  fof(f13,plain,(
% 7.72/1.51    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 7.72/1.51    inference(ennf_transformation,[],[f10])).
% 7.72/1.51  
% 7.72/1.51  fof(f20,plain,(
% 7.72/1.51    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 7.72/1.51    inference(nnf_transformation,[],[f13])).
% 7.72/1.51  
% 7.72/1.51  fof(f21,plain,(
% 7.72/1.51    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((k4_xboole_0(sK1,sK2) != sK1 | ~r1_xboole_0(sK1,sK2)) & (k4_xboole_0(sK1,sK2) = sK1 | r1_xboole_0(sK1,sK2)))),
% 7.72/1.51    introduced(choice_axiom,[])).
% 7.72/1.51  
% 7.72/1.51  fof(f22,plain,(
% 7.72/1.51    (k4_xboole_0(sK1,sK2) != sK1 | ~r1_xboole_0(sK1,sK2)) & (k4_xboole_0(sK1,sK2) = sK1 | r1_xboole_0(sK1,sK2))),
% 7.72/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f21])).
% 7.72/1.51  
% 7.72/1.51  fof(f36,plain,(
% 7.72/1.51    k4_xboole_0(sK1,sK2) = sK1 | r1_xboole_0(sK1,sK2)),
% 7.72/1.51    inference(cnf_transformation,[],[f22])).
% 7.72/1.51  
% 7.72/1.51  fof(f8,axiom,(
% 7.72/1.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.72/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.51  
% 7.72/1.51  fof(f35,plain,(
% 7.72/1.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.72/1.51    inference(cnf_transformation,[],[f8])).
% 7.72/1.51  
% 7.72/1.51  fof(f29,plain,(
% 7.72/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.72/1.51    inference(cnf_transformation,[],[f18])).
% 7.72/1.51  
% 7.72/1.51  fof(f3,axiom,(
% 7.72/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.72/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.51  
% 7.72/1.51  fof(f19,plain,(
% 7.72/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.72/1.51    inference(nnf_transformation,[],[f3])).
% 7.72/1.51  
% 7.72/1.51  fof(f30,plain,(
% 7.72/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.72/1.51    inference(cnf_transformation,[],[f19])).
% 7.72/1.51  
% 7.72/1.51  fof(f40,plain,(
% 7.72/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.72/1.51    inference(definition_unfolding,[],[f30,f34])).
% 7.72/1.51  
% 7.72/1.51  fof(f37,plain,(
% 7.72/1.51    k4_xboole_0(sK1,sK2) != sK1 | ~r1_xboole_0(sK1,sK2)),
% 7.72/1.51    inference(cnf_transformation,[],[f22])).
% 7.72/1.51  
% 7.72/1.51  cnf(c_178,plain,
% 7.72/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.72/1.51      theory(equality) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_3164,plain,
% 7.72/1.51      ( r2_hidden(X0,X1)
% 7.72/1.51      | ~ r2_hidden(sK0(X2,X3,X4),X5)
% 7.72/1.51      | X1 != X5
% 7.72/1.51      | X0 != sK0(X2,X3,X4) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_178]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_7413,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,X0),X1)
% 7.72/1.51      | r2_hidden(sK0(sK1,sK2,X0),X2)
% 7.72/1.51      | X2 != X1
% 7.72/1.51      | sK0(sK1,sK2,X0) != sK0(sK1,sK2,X0) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_3164]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_17571,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,X0),X1)
% 7.72/1.51      | r2_hidden(sK0(sK1,sK2,X0),k4_xboole_0(X2,sK1))
% 7.72/1.51      | sK0(sK1,sK2,X0) != sK0(sK1,sK2,X0)
% 7.72/1.51      | k4_xboole_0(X2,sK1) != X1 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_7413]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_28794,plain,
% 7.72/1.51      ( r2_hidden(sK0(sK1,sK2,X0),k4_xboole_0(X1,sK1))
% 7.72/1.51      | ~ r2_hidden(sK0(sK1,sK2,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 7.72/1.51      | sK0(sK1,sK2,X0) != sK0(sK1,sK2,X0)
% 7.72/1.51      | k4_xboole_0(X1,sK1) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_17571]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_28797,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 7.72/1.51      | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,sK1))
% 7.72/1.51      | sK0(sK1,sK2,sK1) != sK0(sK1,sK2,sK1)
% 7.72/1.51      | k4_xboole_0(sK1,sK1) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_28794]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_176,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1903,plain,
% 7.72/1.51      ( X0 != X1 | k4_xboole_0(X2,X3) != X1 | k4_xboole_0(X2,X3) = X0 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_176]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_4067,plain,
% 7.72/1.51      ( X0 != k4_xboole_0(X1,X2)
% 7.72/1.51      | k4_xboole_0(X3,X4) = X0
% 7.72/1.51      | k4_xboole_0(X3,X4) != k4_xboole_0(X1,X2) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_1903]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_15666,plain,
% 7.72/1.51      ( k4_xboole_0(X0,X1) != k4_xboole_0(X2,X3)
% 7.72/1.51      | k4_xboole_0(X0,X1) = k1_xboole_0
% 7.72/1.51      | k1_xboole_0 != k4_xboole_0(X2,X3) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_4067]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_15672,plain,
% 7.72/1.51      ( k4_xboole_0(sK1,sK1) != k4_xboole_0(sK1,sK1)
% 7.72/1.51      | k4_xboole_0(sK1,sK1) = k1_xboole_0
% 7.72/1.51      | k1_xboole_0 != k4_xboole_0(sK1,sK1) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_15666]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_175,plain,( X0 = X0 ),theory(equality) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_863,plain,
% 7.72/1.51      ( X0 != X1 | X1 = X0 ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_176,c_175]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_10,plain,
% 7.72/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.72/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_2735,plain,
% 7.72/1.51      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_863,c_10]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_3389,plain,
% 7.72/1.51      ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
% 7.72/1.51      | k1_xboole_0 = X0 ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_2735,c_176]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_3,plain,
% 7.72/1.51      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.72/1.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.72/1.51      | k4_xboole_0(X0,X1) = X2 ),
% 7.72/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1001,plain,
% 7.72/1.51      ( r2_hidden(sK0(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0 ),
% 7.72/1.51      inference(factoring,[status(thm)],[c_3]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_2886,plain,
% 7.72/1.51      ( r2_hidden(sK0(X0,X1,X0),X0) | X0 = k4_xboole_0(X0,X1) ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_1001,c_863]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_5906,plain,
% 7.72/1.51      ( r2_hidden(sK0(X0,k4_xboole_0(X0,k1_xboole_0),X0),X0)
% 7.72/1.51      | k1_xboole_0 = X0 ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_3389,c_2886]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_6,plain,
% 7.72/1.51      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.72/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_5925,plain,
% 7.72/1.51      ( r2_hidden(sK0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(X0,X1)),X0)
% 7.72/1.51      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_5906,c_6]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_5927,plain,
% 7.72/1.51      ( r2_hidden(sK0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k1_xboole_0),k4_xboole_0(sK1,sK1)),sK1)
% 7.72/1.51      | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_5925]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_5,plain,
% 7.72/1.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.72/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_5921,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(X0,X1)),X1)
% 7.72/1.51      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_5906,c_5]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_5923,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k1_xboole_0),k4_xboole_0(sK1,sK1)),sK1)
% 7.72/1.51      | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_5921]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_4,plain,
% 7.72/1.51      ( ~ r2_hidden(X0,X1)
% 7.72/1.51      | r2_hidden(X0,X2)
% 7.72/1.51      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 7.72/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1450,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,sK1),X0)
% 7.72/1.51      | r2_hidden(sK0(sK1,sK2,sK1),X1)
% 7.72/1.51      | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X0,X1)) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_3292,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,sK1),X0)
% 7.72/1.51      | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X0,k4_xboole_0(X1,sK2)))
% 7.72/1.51      | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X1,sK2)) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_1450]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_3294,plain,
% 7.72/1.51      ( r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 7.72/1.51      | r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,sK2))
% 7.72/1.51      | ~ r2_hidden(sK0(sK1,sK2,sK1),sK1) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_3292]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1291,plain,
% 7.72/1.51      ( X0 != X1 | X0 = k4_xboole_0(X2,X3) | k4_xboole_0(X2,X3) != X1 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_176]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1911,plain,
% 7.72/1.51      ( X0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 7.72/1.51      | X0 != k1_xboole_0
% 7.72/1.51      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_1291]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_3011,plain,
% 7.72/1.51      ( k4_xboole_0(X0,X1) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 7.72/1.51      | k4_xboole_0(X0,X1) != k1_xboole_0
% 7.72/1.51      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_1911]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_3012,plain,
% 7.72/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k1_xboole_0
% 7.72/1.51      | k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 7.72/1.51      | k4_xboole_0(sK1,sK1) != k1_xboole_0 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_3011]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_13,negated_conjecture,
% 7.72/1.51      ( r1_xboole_0(sK1,sK2) | k4_xboole_0(sK1,sK2) = sK1 ),
% 7.72/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_861,plain,
% 7.72/1.51      ( r1_xboole_0(sK1,sK2) | X0 != sK1 | k4_xboole_0(sK1,sK2) = X0 ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_176,c_13]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1830,plain,
% 7.72/1.51      ( r1_xboole_0(sK1,sK2)
% 7.72/1.51      | ~ r2_hidden(X0,X1)
% 7.72/1.51      | r2_hidden(X2,k4_xboole_0(sK1,sK2))
% 7.72/1.51      | X2 != X0
% 7.72/1.51      | X1 != sK1 ),
% 7.72/1.51      inference(resolution,[status(thm)],[c_178,c_861]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_184,plain,
% 7.72/1.51      ( sK1 = sK1 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_175]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_943,plain,
% 7.72/1.51      ( k4_xboole_0(sK1,sK2) != X0
% 7.72/1.51      | sK1 != X0
% 7.72/1.51      | sK1 = k4_xboole_0(sK1,sK2) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_176]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_944,plain,
% 7.72/1.51      ( k4_xboole_0(sK1,sK2) != sK1
% 7.72/1.51      | sK1 = k4_xboole_0(sK1,sK2)
% 7.72/1.51      | sK1 != sK1 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_943]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1031,plain,
% 7.72/1.51      ( sK2 = sK2 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_175]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_179,plain,
% 7.72/1.51      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.72/1.51      theory(equality) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_591,plain,
% 7.72/1.51      ( r1_xboole_0(X0,X1)
% 7.72/1.51      | ~ r1_xboole_0(k4_xboole_0(X2,X3),X3)
% 7.72/1.51      | X1 != X3
% 7.72/1.51      | X0 != k4_xboole_0(X2,X3) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_179]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_666,plain,
% 7.72/1.51      ( ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
% 7.72/1.51      | r1_xboole_0(sK1,sK2)
% 7.72/1.51      | sK2 != X1
% 7.72/1.51      | sK1 != k4_xboole_0(X0,X1) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_591]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1368,plain,
% 7.72/1.51      ( ~ r1_xboole_0(k4_xboole_0(X0,sK2),sK2)
% 7.72/1.51      | r1_xboole_0(sK1,sK2)
% 7.72/1.51      | sK2 != sK2
% 7.72/1.51      | sK1 != k4_xboole_0(X0,sK2) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_666]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1371,plain,
% 7.72/1.51      ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
% 7.72/1.51      | r1_xboole_0(sK1,sK2)
% 7.72/1.51      | sK2 != sK2
% 7.72/1.51      | sK1 != k4_xboole_0(sK1,sK2) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_1368]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_11,plain,
% 7.72/1.51      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.72/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_2332,plain,
% 7.72/1.51      ( r1_xboole_0(k4_xboole_0(X0,sK2),sK2) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_2334,plain,
% 7.72/1.51      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_2332]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_2553,plain,
% 7.72/1.51      ( r1_xboole_0(sK1,sK2) ),
% 7.72/1.51      inference(global_propositional_subsumption,
% 7.72/1.51                [status(thm)],
% 7.72/1.51                [c_1830,c_13,c_184,c_944,c_1031,c_1371,c_2334]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1470,plain,
% 7.72/1.51      ( sK0(sK1,sK2,sK1) = sK0(sK1,sK2,sK1) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_175]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_929,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X0,sK2))
% 7.72/1.51      | ~ r2_hidden(sK0(sK1,sK2,sK1),sK2) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_931,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,sK2))
% 7.72/1.51      | ~ r2_hidden(sK0(sK1,sK2,sK1),sK2) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_929]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_905,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(X0,sK1))
% 7.72/1.51      | ~ r2_hidden(sK0(sK1,sK2,sK1),sK1) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_907,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(sK1,sK2,sK1),k4_xboole_0(sK1,sK1))
% 7.72/1.51      | ~ r2_hidden(sK0(sK1,sK2,sK1),sK1) ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_905]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_1,plain,
% 7.72/1.51      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.72/1.51      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.72/1.51      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.72/1.51      | k4_xboole_0(X0,X1) = X2 ),
% 7.72/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_900,plain,
% 7.72/1.51      ( r2_hidden(sK0(sK1,sK2,sK1),sK2)
% 7.72/1.51      | ~ r2_hidden(sK0(sK1,sK2,sK1),sK1)
% 7.72/1.51      | k4_xboole_0(sK1,sK2) = sK1 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_738,plain,
% 7.72/1.51      ( r2_hidden(sK0(sK1,sK2,sK1),sK1) | k4_xboole_0(sK1,sK2) = sK1 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_8,plain,
% 7.72/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.72/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.72/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_708,plain,
% 7.72/1.51      ( ~ r1_xboole_0(sK1,sK2)
% 7.72/1.51      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_177,plain,
% 7.72/1.51      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 7.72/1.51      theory(equality) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_180,plain,
% 7.72/1.51      ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) | sK1 != sK1 ),
% 7.72/1.51      inference(instantiation,[status(thm)],[c_177]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(c_12,negated_conjecture,
% 7.72/1.51      ( ~ r1_xboole_0(sK1,sK2) | k4_xboole_0(sK1,sK2) != sK1 ),
% 7.72/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.72/1.51  
% 7.72/1.51  cnf(contradiction,plain,
% 7.72/1.51      ( $false ),
% 7.72/1.51      inference(minisat,
% 7.72/1.51                [status(thm)],
% 7.72/1.51                [c_28797,c_15672,c_5927,c_5923,c_3294,c_3012,c_2553,
% 7.72/1.51                 c_1470,c_931,c_907,c_900,c_738,c_708,c_184,c_180,c_12]) ).
% 7.72/1.51  
% 7.72/1.51  
% 7.72/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.72/1.51  
% 7.72/1.51  ------                               Statistics
% 7.72/1.51  
% 7.72/1.51  ------ Selected
% 7.72/1.51  
% 7.72/1.51  total_time:                             0.715
% 7.72/1.51  
%------------------------------------------------------------------------------

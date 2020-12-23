%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0085+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:19 EST 2020

% Result     : Theorem 11.55s
% Output     : CNFRefutation 11.55s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 173 expanded)
%              Number of clauses        :   48 (  50 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  433 ( 763 expanded)
%              Number of equality atoms :   93 ( 162 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f136,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f136])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f223])).

fof(f225,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f224,f225])).

fof(f282,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f226])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f232,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f233,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f232])).

fof(f234,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f233])).

fof(f235,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f236,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f234,f235])).

fof(f293,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f236])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f398,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f448,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f293,f398])).

fof(f522,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f448])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f144,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f336,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f32,axiom,(
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

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f256,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f142,f256])).

fof(f330,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f257])).

fof(f68,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f378,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f491,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f378,f398,f398])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f152,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f350,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f152])).

fof(f74,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f271,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f74])).

fof(f385,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f271])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f281,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f492,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f385,f281])).

fof(f384,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f271])).

fof(f493,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f384,f281])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f227,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f228,plain,(
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
    inference(flattening,[],[f227])).

fof(f229,plain,(
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
    inference(rectify,[],[f228])).

fof(f230,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f231,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f229,f230])).

fof(f285,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f231])).

fof(f521,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f285])).

fof(f90,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f401,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f90])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f276,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f291,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f236])).

fof(f450,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f291,f398])).

fof(f524,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f450])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f236])).

fof(f445,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f296,f398])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f236])).

fof(f447,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f294,f398])).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f236])).

fof(f446,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f295,f398])).

fof(f122,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f123,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f122])).

fof(f213,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f123])).

fof(f272,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK15,sK17) != k3_xboole_0(sK15,k2_xboole_0(sK16,sK17))
      & r1_xboole_0(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f273,plain,
    ( k3_xboole_0(sK15,sK17) != k3_xboole_0(sK15,k2_xboole_0(sK16,sK17))
    & r1_xboole_0(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f213,f272])).

fof(f437,plain,(
    k3_xboole_0(sK15,sK17) != k3_xboole_0(sK15,k2_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f273])).

fof(f518,plain,(
    k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK16,sK17))) ),
    inference(definition_unfolding,[],[f437,f398,f398])).

fof(f436,plain,(
    r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f273])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f282])).

cnf(c_7469,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),X0)
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),X0)
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_38634,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16))
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k2_xboole_0(sK17,sK16)) ),
    inference(instantiation,[status(thm)],[c_7469])).

cnf(c_38639,plain,
    ( r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16)) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k2_xboole_0(sK17,sK16)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38634])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f522])).

cnf(c_9558,plain,
    ( ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),X0)
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,X0)))
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_19702,plain,
    ( r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK17)
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_9558])).

cnf(c_19703,plain,
    ( r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) = iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK17) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19702])).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f336])).

cnf(c_52,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f330])).

cnf(c_766,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r1_xboole_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57,c_52])).

cnf(c_767,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_766])).

cnf(c_9548,plain,
    ( ~ r1_xboole_0(sK15,X0)
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),X0)
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_19682,plain,
    ( ~ r1_xboole_0(sK15,sK16)
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK16)
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_9548])).

cnf(c_19683,plain,
    ( r1_xboole_0(sK15,sK16) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK16) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19682])).

cnf(c_102,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f491])).

cnf(c_13299,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k2_xboole_0(sK17,sK16)) ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_74,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f350])).

cnf(c_9683,plain,
    ( r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16))
    | ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),X0),k2_xboole_0(sK17,sK16)) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_13298,plain,
    ( r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16))
    | ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))),k2_xboole_0(sK17,sK16)) ),
    inference(instantiation,[status(thm)],[c_9683])).

cnf(c_108,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f492])).

cnf(c_12568,plain,
    ( ~ r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16))
    | k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_109,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f493])).

cnf(c_9684,plain,
    ( r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16))
    | k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_9685,plain,
    ( k4_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16)) != o_0_0_xboole_0
    | r1_tarski(k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)),k2_xboole_0(sK17,sK16)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9684])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f521])).

cnf(c_124,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f401])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f276])).

cnf(c_2587,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_124,c_2])).

cnf(c_9508,plain,
    ( ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k2_xboole_0(sK17,sK16))
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK16)
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK17) ),
    inference(instantiation,[status(thm)],[c_2587])).

cnf(c_9509,plain,
    ( r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k2_xboole_0(sK17,sK16)) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK16) = iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK17) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9508])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f524])).

cnf(c_7495,plain,
    ( ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_7496,plain,
    ( r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7495])).

cnf(c_16,plain,
    ( ~ r2_hidden(sK3(X0,X1,X2),X1)
    | ~ r2_hidden(sK3(X0,X1,X2),X0)
    | ~ r2_hidden(sK3(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f445])).

cnf(c_7479,plain,
    ( ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k2_xboole_0(sK17,sK16))
    | ~ r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15)
    | k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK17,sK16))) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_7480,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK17,sK16))) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k2_xboole_0(sK17,sK16)) != iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7479])).

cnf(c_18,plain,
    ( r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK3(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f447])).

cnf(c_6172,plain,
    ( r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15)
    | k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK17,sK16))) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6173,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK17,sK16))) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) = iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6172])).

cnf(c_17,plain,
    ( r2_hidden(sK3(X0,X1,X2),X1)
    | r2_hidden(sK3(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f446])).

cnf(c_6065,plain,
    ( r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)))
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k2_xboole_0(sK17,sK16))
    | k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK17,sK16))) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_6066,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK17,sK16))) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))) = iProver_top
    | r2_hidden(sK3(sK15,k2_xboole_0(sK17,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK17))),k2_xboole_0(sK17,sK16)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6065])).

cnf(c_159,negated_conjecture,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)) != k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK16,sK17))) ),
    inference(cnf_transformation,[],[f518])).

cnf(c_2570,negated_conjecture,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK17,sK16))) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK17)) ),
    inference(theory_normalisation,[status(thm)],[c_159,c_124,c_2])).

cnf(c_160,negated_conjecture,
    ( r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f436])).

cnf(c_166,plain,
    ( r1_xboole_0(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38639,c_19703,c_19683,c_13299,c_13298,c_12568,c_9685,c_9509,c_7496,c_7480,c_6173,c_6066,c_2570,c_166])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:11 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   50 (  90 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  223 ( 461 expanded)
%              Number of equality atoms :   59 ( 114 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X1,X2) )
       => ( r1_tarski(X1,k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f7])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X1,k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & ! [X2] :
            ( r1_tarski(X1,X2)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_tarski(sK5,k1_setfam_1(sK4))
      & k1_xboole_0 != sK4
      & ! [X2] :
          ( r1_tarski(sK5,X2)
          | ~ r2_hidden(X2,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(sK5,k1_setfam_1(sK4))
    & k1_xboole_0 != sK4
    & ! [X2] :
        ( r1_tarski(sK5,X2)
        | ~ r2_hidden(X2,sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f19])).

fof(f32,plain,(
    ! [X2] :
      ( r1_tarski(sK5,X2)
      | ~ r2_hidden(X2,sK4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f9])).

fof(f13,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK2(X0,X5))
        & r2_hidden(sK2(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK0(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK0(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK0(X0,X1),sK1(X0,X1))
                  & r2_hidden(sK1(X0,X1),X0) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK0(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK2(X0,X5))
                    & r2_hidden(sK2(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13,f12,f11])).

fof(f23,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK2(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f23])).

fof(f22,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK2(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK2(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ~ r1_tarski(sK5,k1_setfam_1(sK4)) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_696,plain,
    ( ~ r1_tarski(sK5,X0)
    | r2_hidden(sK3(sK5,k1_setfam_1(sK4)),X0)
    | ~ r2_hidden(sK3(sK5,k1_setfam_1(sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_896,plain,
    ( ~ r1_tarski(sK5,sK2(sK4,sK3(sK5,k1_setfam_1(sK4))))
    | r2_hidden(sK3(sK5,k1_setfam_1(sK4)),sK2(sK4,sK3(sK5,k1_setfam_1(sK4))))
    | ~ r2_hidden(sK3(sK5,k1_setfam_1(sK4)),sK5) ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK5,X0)
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_761,plain,
    ( r1_tarski(sK5,sK2(sK4,sK3(sK5,k1_setfam_1(sK4))))
    | ~ r2_hidden(sK2(sK4,sK3(sK5,k1_setfam_1(sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,sK2(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_652,plain,
    ( ~ r2_hidden(X0,sK2(sK4,X0))
    | r2_hidden(X0,k1_setfam_1(sK4))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_723,plain,
    ( ~ r2_hidden(sK3(sK5,k1_setfam_1(sK4)),sK2(sK4,sK3(sK5,k1_setfam_1(sK4))))
    | r2_hidden(sK3(sK5,k1_setfam_1(sK4)),k1_setfam_1(sK4))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK2(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_657,plain,
    ( r2_hidden(X0,k1_setfam_1(sK4))
    | r2_hidden(sK2(sK4,X0),sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_716,plain,
    ( r2_hidden(sK3(sK5,k1_setfam_1(sK4)),k1_setfam_1(sK4))
    | r2_hidden(sK2(sK4,sK3(sK5,k1_setfam_1(sK4))),sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK5,k1_setfam_1(sK4)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_158,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | k1_setfam_1(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_159,plain,
    ( ~ r2_hidden(sK3(sK5,k1_setfam_1(sK4)),k1_setfam_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_151,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | k1_setfam_1(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_152,plain,
    ( r2_hidden(sK3(sK5,k1_setfam_1(sK4)),sK5) ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_896,c_761,c_723,c_716,c_159,c_152,c_12])).


%------------------------------------------------------------------------------

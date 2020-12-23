%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0384+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:10 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 110 expanded)
%              Number of equality atoms :   47 (  47 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    k1_xboole_0 != k1_setfam_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    k1_xboole_0 != k1_setfam_1(k1_xboole_0) ),
    inference(flattening,[],[f3])).

fof(f20,plain,(
    k1_xboole_0 != k1_setfam_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f6,plain,(
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

fof(f7,plain,(
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
    inference(rectify,[],[f6])).

fof(f10,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK2(X0,X5))
        & r2_hidden(sK2(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
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

fof(f11,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10,f9,f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f18])).

fof(f24,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != k1_setfam_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_227,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_1])).

cnf(c_228,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_227])).


%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:41:21 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 181 expanded)
%              Number of clauses        :   38 (  67 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  314 ( 719 expanded)
%              Number of equality atoms :  120 ( 229 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK6(X0,X5))
        & r2_hidden(sK6(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
              ( ~ r2_hidden(sK4(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK4(X0,X1),sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),X0) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK4(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK6(X0,X5))
                    & r2_hidden(sK6(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).

fof(f40,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f33])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,conjecture,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,
    ( ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0))
   => ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f12,f27])).

fof(f48,plain,(
    ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f53,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_761,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_747,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1030,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(sK0(k1_setfam_1(X0),X2),X1) = iProver_top
    | r1_tarski(k1_setfam_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_747])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_757,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1488,plain,
    ( r2_hidden(X0,sK0(X1,X2)) != iProver_top
    | r2_hidden(X0,k3_tarski(X1)) = iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_757])).

cnf(c_2503,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X1,X2),X0) != iProver_top
    | r2_hidden(sK0(k1_setfam_1(X0),X3),k3_tarski(X1)) = iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k1_setfam_1(X0),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1030,c_1488])).

cnf(c_17792,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_setfam_1(X0),X1),k3_tarski(X0)) = iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k1_setfam_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_2503])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_762,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_18029,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17792,c_762])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_746,plain,
    ( r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18050,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18029,c_746])).

cnf(c_840,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_0,c_1])).

cnf(c_842,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_444,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_918,plain,
    ( k1_setfam_1(sK7) = k1_setfam_1(X0)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_923,plain,
    ( k1_setfam_1(sK7) = k1_setfam_1(k1_xboole_0)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_443,plain,
    ( X0 != X1
    | k3_tarski(X0) = k3_tarski(X1) ),
    theory(equality)).

cnf(c_1432,plain,
    ( k3_tarski(sK7) = k3_tarski(X0)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1437,plain,
    ( k3_tarski(sK7) = k3_tarski(k1_xboole_0)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_441,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2084,plain,
    ( r1_tarski(X0,k3_tarski(k1_xboole_0))
    | ~ r1_tarski(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_441,c_10])).

cnf(c_11,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2893,plain,
    ( r1_tarski(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2084,c_11])).

cnf(c_863,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
    | k1_setfam_1(sK7) != X0
    | k3_tarski(sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_917,plain,
    ( ~ r1_tarski(k1_setfam_1(X0),X1)
    | r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
    | k1_setfam_1(sK7) != k1_setfam_1(X0)
    | k3_tarski(sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_3075,plain,
    ( ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X1))
    | r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
    | k1_setfam_1(sK7) != k1_setfam_1(X0)
    | k3_tarski(sK7) != k3_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_917])).

cnf(c_3077,plain,
    ( r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
    | ~ r1_tarski(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0))
    | k1_setfam_1(sK7) != k1_setfam_1(k1_xboole_0)
    | k3_tarski(sK7) != k3_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3075])).

cnf(c_18241,plain,
    ( r1_tarski(sK7,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18050,c_19,c_842,c_923,c_1437,c_2893,c_3077])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_754,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18247,plain,
    ( sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18241,c_754])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18247,c_3077,c_2893,c_1437,c_923,c_842,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.62/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.49  
% 7.62/1.49  ------  iProver source info
% 7.62/1.49  
% 7.62/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.49  git: non_committed_changes: false
% 7.62/1.49  git: last_make_outside_of_git: false
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  ------ Parsing...
% 7.62/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  ------ Proving...
% 7.62/1.49  ------ Problem Properties 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  clauses                                 19
% 7.62/1.49  conjectures                             1
% 7.62/1.49  EPR                                     0
% 7.62/1.49  Horn                                    10
% 7.62/1.49  unary                                   3
% 7.62/1.49  binary                                  6
% 7.62/1.49  lits                                    51
% 7.62/1.49  lits eq                                 16
% 7.62/1.49  fd_pure                                 0
% 7.62/1.49  fd_pseudo                               0
% 7.62/1.49  fd_cond                                 5
% 7.62/1.49  fd_pseudo_cond                          6
% 7.62/1.49  AC symbols                              0
% 7.62/1.49  
% 7.62/1.49  ------ Input Options Time Limit: Unbounded
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  Current options:
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS status Theorem for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  fof(f1,axiom,(
% 7.62/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f8,plain,(
% 7.62/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.62/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 7.62/1.49  
% 7.62/1.49  fof(f9,plain,(
% 7.62/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.62/1.49    inference(ennf_transformation,[],[f8])).
% 7.62/1.49  
% 7.62/1.49  fof(f13,plain,(
% 7.62/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f14,plain,(
% 7.62/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 7.62/1.49  
% 7.62/1.49  fof(f29,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f14])).
% 7.62/1.49  
% 7.62/1.49  fof(f5,axiom,(
% 7.62/1.49    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f11,plain,(
% 7.62/1.49    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 7.62/1.49    inference(ennf_transformation,[],[f5])).
% 7.62/1.49  
% 7.62/1.49  fof(f21,plain,(
% 7.62/1.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.62/1.49    inference(nnf_transformation,[],[f11])).
% 7.62/1.49  
% 7.62/1.49  fof(f22,plain,(
% 7.62/1.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.62/1.49    inference(rectify,[],[f21])).
% 7.62/1.49  
% 7.62/1.49  fof(f25,plain,(
% 7.62/1.49    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0)))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f24,plain,(
% 7.62/1.49    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)))) )),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f23,plain,(
% 7.62/1.49    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK4(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1))))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f26,plain,(
% 7.62/1.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK5(X0,X1),X0)) | ~r2_hidden(sK4(X0,X1),X1)) & (! [X4] : (r2_hidden(sK4(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK6(X0,X5)) & r2_hidden(sK6(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).
% 7.62/1.49  
% 7.62/1.49  fof(f40,plain,(
% 7.62/1.49    ( ! [X0,X7,X5,X1] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,X1) | k1_setfam_1(X0) != X1 | k1_xboole_0 = X0) )),
% 7.62/1.49    inference(cnf_transformation,[],[f26])).
% 7.62/1.49  
% 7.62/1.49  fof(f58,plain,(
% 7.62/1.49    ( ! [X0,X7,X5] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0) | ~r2_hidden(X5,k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 7.62/1.49    inference(equality_resolution,[],[f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f2,axiom,(
% 7.62/1.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f15,plain,(
% 7.62/1.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 7.62/1.49    inference(nnf_transformation,[],[f2])).
% 7.62/1.49  
% 7.62/1.49  fof(f16,plain,(
% 7.62/1.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.62/1.49    inference(rectify,[],[f15])).
% 7.62/1.49  
% 7.62/1.49  fof(f19,plain,(
% 7.62/1.49    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f18,plain,(
% 7.62/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f17,plain,(
% 7.62/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f20,plain,(
% 7.62/1.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 7.62/1.49  
% 7.62/1.49  fof(f33,plain,(
% 7.62/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 7.62/1.49    inference(cnf_transformation,[],[f20])).
% 7.62/1.49  
% 7.62/1.49  fof(f49,plain,(
% 7.62/1.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 7.62/1.49    inference(equality_resolution,[],[f33])).
% 7.62/1.49  
% 7.62/1.49  fof(f30,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f14])).
% 7.62/1.49  
% 7.62/1.49  fof(f6,conjecture,(
% 7.62/1.49    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f7,negated_conjecture,(
% 7.62/1.49    ~! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 7.62/1.49    inference(negated_conjecture,[],[f6])).
% 7.62/1.49  
% 7.62/1.49  fof(f12,plain,(
% 7.62/1.49    ? [X0] : ~r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 7.62/1.49    inference(ennf_transformation,[],[f7])).
% 7.62/1.49  
% 7.62/1.49  fof(f27,plain,(
% 7.62/1.49    ? [X0] : ~r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) => ~r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f28,plain,(
% 7.62/1.49    ~r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f12,f27])).
% 7.62/1.49  
% 7.62/1.49  fof(f48,plain,(
% 7.62/1.49    ~r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))),
% 7.62/1.49    inference(cnf_transformation,[],[f28])).
% 7.62/1.49  
% 7.62/1.49  fof(f4,axiom,(
% 7.62/1.49    k3_tarski(k1_xboole_0) = k1_xboole_0),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f39,plain,(
% 7.62/1.49    k3_tarski(k1_xboole_0) = k1_xboole_0),
% 7.62/1.49    inference(cnf_transformation,[],[f4])).
% 7.62/1.49  
% 7.62/1.49  fof(f47,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | k1_xboole_0 != X1 | k1_xboole_0 != X0) )),
% 7.62/1.49    inference(cnf_transformation,[],[f26])).
% 7.62/1.49  
% 7.62/1.49  fof(f52,plain,(
% 7.62/1.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(X0) | k1_xboole_0 != X0) )),
% 7.62/1.49    inference(equality_resolution,[],[f47])).
% 7.62/1.49  
% 7.62/1.49  fof(f53,plain,(
% 7.62/1.49    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 7.62/1.49    inference(equality_resolution,[],[f52])).
% 7.62/1.49  
% 7.62/1.49  fof(f3,axiom,(
% 7.62/1.49    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f10,plain,(
% 7.62/1.49    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f3])).
% 7.62/1.49  
% 7.62/1.49  fof(f38,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f10])).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1,plain,
% 7.62/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_761,plain,
% 7.62/1.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.62/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_18,plain,
% 7.62/1.49      ( ~ r2_hidden(X0,X1)
% 7.62/1.49      | r2_hidden(X2,X0)
% 7.62/1.49      | ~ r2_hidden(X2,k1_setfam_1(X1))
% 7.62/1.49      | k1_xboole_0 = X1 ),
% 7.62/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_747,plain,
% 7.62/1.49      ( k1_xboole_0 = X0
% 7.62/1.49      | r2_hidden(X1,X0) != iProver_top
% 7.62/1.49      | r2_hidden(X2,X1) = iProver_top
% 7.62/1.49      | r2_hidden(X2,k1_setfam_1(X0)) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1030,plain,
% 7.62/1.49      ( k1_xboole_0 = X0
% 7.62/1.49      | r2_hidden(X1,X0) != iProver_top
% 7.62/1.49      | r2_hidden(sK0(k1_setfam_1(X0),X2),X1) = iProver_top
% 7.62/1.49      | r1_tarski(k1_setfam_1(X0),X2) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_761,c_747]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5,plain,
% 7.62/1.49      ( ~ r2_hidden(X0,X1)
% 7.62/1.49      | ~ r2_hidden(X2,X0)
% 7.62/1.49      | r2_hidden(X2,k3_tarski(X1)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_757,plain,
% 7.62/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.62/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.62/1.49      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1488,plain,
% 7.62/1.49      ( r2_hidden(X0,sK0(X1,X2)) != iProver_top
% 7.62/1.49      | r2_hidden(X0,k3_tarski(X1)) = iProver_top
% 7.62/1.49      | r1_tarski(X1,X2) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_761,c_757]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2503,plain,
% 7.62/1.49      ( k1_xboole_0 = X0
% 7.62/1.49      | r2_hidden(sK0(X1,X2),X0) != iProver_top
% 7.62/1.49      | r2_hidden(sK0(k1_setfam_1(X0),X3),k3_tarski(X1)) = iProver_top
% 7.62/1.49      | r1_tarski(X1,X2) = iProver_top
% 7.62/1.49      | r1_tarski(k1_setfam_1(X0),X3) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1030,c_1488]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17792,plain,
% 7.62/1.49      ( k1_xboole_0 = X0
% 7.62/1.49      | r2_hidden(sK0(k1_setfam_1(X0),X1),k3_tarski(X0)) = iProver_top
% 7.62/1.49      | r1_tarski(X0,X2) = iProver_top
% 7.62/1.49      | r1_tarski(k1_setfam_1(X0),X1) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_761,c_2503]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_0,plain,
% 7.62/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_762,plain,
% 7.62/1.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.62/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_18029,plain,
% 7.62/1.49      ( k1_xboole_0 = X0
% 7.62/1.49      | r1_tarski(X0,X1) = iProver_top
% 7.62/1.49      | r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_17792,c_762]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_19,negated_conjecture,
% 7.62/1.49      ( ~ r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_746,plain,
% 7.62/1.49      ( r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7)) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_18050,plain,
% 7.62/1.49      ( sK7 = k1_xboole_0 | r1_tarski(sK7,X0) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_18029,c_746]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_840,plain,
% 7.62/1.49      ( r1_tarski(X0,X0) ),
% 7.62/1.49      inference(resolution,[status(thm)],[c_0,c_1]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_842,plain,
% 7.62/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_840]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_444,plain,
% 7.62/1.49      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 7.62/1.49      theory(equality) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_918,plain,
% 7.62/1.49      ( k1_setfam_1(sK7) = k1_setfam_1(X0) | sK7 != X0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_444]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_923,plain,
% 7.62/1.49      ( k1_setfam_1(sK7) = k1_setfam_1(k1_xboole_0)
% 7.62/1.49      | sK7 != k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_918]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_443,plain,
% 7.62/1.49      ( X0 != X1 | k3_tarski(X0) = k3_tarski(X1) ),
% 7.62/1.49      theory(equality) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1432,plain,
% 7.62/1.49      ( k3_tarski(sK7) = k3_tarski(X0) | sK7 != X0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_443]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1437,plain,
% 7.62/1.49      ( k3_tarski(sK7) = k3_tarski(k1_xboole_0) | sK7 != k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1432]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_441,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.62/1.49      theory(equality) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10,plain,
% 7.62/1.49      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2084,plain,
% 7.62/1.49      ( r1_tarski(X0,k3_tarski(k1_xboole_0))
% 7.62/1.49      | ~ r1_tarski(X1,k1_xboole_0)
% 7.62/1.49      | X0 != X1 ),
% 7.62/1.49      inference(resolution,[status(thm)],[c_441,c_10]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11,plain,
% 7.62/1.49      ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2893,plain,
% 7.62/1.49      ( r1_tarski(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0))
% 7.62/1.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.62/1.49      inference(resolution,[status(thm)],[c_2084,c_11]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_863,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1)
% 7.62/1.49      | r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
% 7.62/1.49      | k1_setfam_1(sK7) != X0
% 7.62/1.49      | k3_tarski(sK7) != X1 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_441]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_917,plain,
% 7.62/1.49      ( ~ r1_tarski(k1_setfam_1(X0),X1)
% 7.62/1.49      | r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
% 7.62/1.49      | k1_setfam_1(sK7) != k1_setfam_1(X0)
% 7.62/1.49      | k3_tarski(sK7) != X1 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_863]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3075,plain,
% 7.62/1.49      ( ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X1))
% 7.62/1.49      | r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
% 7.62/1.49      | k1_setfam_1(sK7) != k1_setfam_1(X0)
% 7.62/1.49      | k3_tarski(sK7) != k3_tarski(X1) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_917]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3077,plain,
% 7.62/1.49      ( r1_tarski(k1_setfam_1(sK7),k3_tarski(sK7))
% 7.62/1.49      | ~ r1_tarski(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0))
% 7.62/1.49      | k1_setfam_1(sK7) != k1_setfam_1(k1_xboole_0)
% 7.62/1.49      | k3_tarski(sK7) != k3_tarski(k1_xboole_0) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_3075]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_18241,plain,
% 7.62/1.49      ( r1_tarski(sK7,X0) = iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_18050,c_19,c_842,c_923,c_1437,c_2893,c_3077]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_754,plain,
% 7.62/1.49      ( k1_xboole_0 = X0
% 7.62/1.49      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_18247,plain,
% 7.62/1.49      ( sK7 = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_18241,c_754]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(contradiction,plain,
% 7.62/1.49      ( $false ),
% 7.62/1.49      inference(minisat,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_18247,c_3077,c_2893,c_1437,c_923,c_842,c_19]) ).
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  ------                               Statistics
% 7.62/1.49  
% 7.62/1.49  ------ Selected
% 7.62/1.49  
% 7.62/1.49  total_time:                             0.645
% 7.62/1.49  
%------------------------------------------------------------------------------

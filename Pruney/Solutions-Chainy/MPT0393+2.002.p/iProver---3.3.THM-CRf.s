%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:33 EST 2020

% Result     : Theorem 19.05s
% Output     : CNFRefutation 19.05s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 172 expanded)
%              Number of clauses        :   58 (  78 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  333 ( 911 expanded)
%              Number of equality atoms :  194 ( 473 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f61])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f158,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f109])).

fof(f20,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f128,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f156,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f110])).

fof(f157,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f156])).

fof(f26,axiom,(
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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f79,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f80,plain,(
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
    inference(rectify,[],[f79])).

fof(f83,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK9(X0,X5))
        & r2_hidden(sK9(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK8(X0,X1))
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
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
              ( ~ r2_hidden(sK7(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK7(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK7(X0,X1),sK8(X0,X1))
                  & r2_hidden(sK8(X0,X1),X0) )
                | ~ r2_hidden(sK7(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK7(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK7(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK9(X0,X5))
                    & r2_hidden(sK9(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f80,f83,f82,f81])).

fof(f138,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK7(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK7(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK7(X0,X1),sK8(X0,X1))
      | ~ r2_hidden(sK7(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK8(X0,X1),X0)
      | ~ r2_hidden(sK7(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f127,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f32])).

fof(f51,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f33])).

fof(f87,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK11)) != sK11 ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    k1_setfam_1(k1_tarski(sK11)) != sK11 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f51,f87])).

fof(f149,plain,(
    k1_setfam_1(k1_tarski(sK11)) != sK11 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1104,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6702,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
    | X0 != sK7(k1_tarski(sK11),sK11)
    | X1 != sK11 ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_13538,plain,
    ( r2_hidden(X0,sK8(k1_tarski(sK11),sK11))
    | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
    | X0 != sK7(k1_tarski(sK11),sK11)
    | sK8(k1_tarski(sK11),sK11) != sK11 ),
    inference(instantiation,[status(thm)],[c_6702])).

cnf(c_54242,plain,
    ( r2_hidden(sK7(k1_tarski(sK11),sK11),sK8(k1_tarski(sK11),sK11))
    | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
    | sK8(k1_tarski(sK11),sK11) != sK11
    | sK7(k1_tarski(sK11),sK11) != sK7(k1_tarski(sK11),sK11) ),
    inference(instantiation,[status(thm)],[c_13538])).

cnf(c_1103,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2494,plain,
    ( X0 != X1
    | k1_tarski(sK11) != X1
    | k1_tarski(sK11) = X0 ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_4945,plain,
    ( X0 != k3_tarski(X1)
    | k1_tarski(sK11) = X0
    | k1_tarski(sK11) != k3_tarski(X1) ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_36709,plain,
    ( k1_tarski(sK11) != k3_tarski(X0)
    | k1_tarski(sK11) = sK11
    | sK11 != k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_4945])).

cnf(c_36710,plain,
    ( k1_tarski(sK11) != k3_tarski(k1_xboole_0)
    | k1_tarski(sK11) = sK11
    | sK11 != k3_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_36709])).

cnf(c_1109,plain,
    ( X0 != X1
    | k3_tarski(X0) = k3_tarski(X1) ),
    theory(equality)).

cnf(c_31100,plain,
    ( X0 != k1_tarski(sK11)
    | k3_tarski(X0) = k3_tarski(k1_tarski(sK11)) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_31101,plain,
    ( k3_tarski(k1_xboole_0) = k3_tarski(k1_tarski(sK11))
    | k1_xboole_0 != k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_31100])).

cnf(c_3114,plain,
    ( X0 != X1
    | X0 = sK11
    | sK11 != X1 ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_13971,plain,
    ( X0 != k1_tarski(sK11)
    | X0 = sK11
    | sK11 != k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_3114])).

cnf(c_13994,plain,
    ( sK11 != k1_tarski(sK11)
    | k1_xboole_0 != k1_tarski(sK11)
    | k1_xboole_0 = sK11 ),
    inference(instantiation,[status(thm)],[c_13971])).

cnf(c_2223,plain,
    ( X0 != X1
    | sK11 != X1
    | sK11 = X0 ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_10565,plain,
    ( X0 != k3_tarski(k1_tarski(sK11))
    | sK11 = X0
    | sK11 != k3_tarski(k1_tarski(sK11)) ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_13074,plain,
    ( k3_tarski(X0) != k3_tarski(k1_tarski(sK11))
    | sK11 = k3_tarski(X0)
    | sK11 != k3_tarski(k1_tarski(sK11)) ),
    inference(instantiation,[status(thm)],[c_10565])).

cnf(c_13075,plain,
    ( k3_tarski(k1_xboole_0) != k3_tarski(k1_tarski(sK11))
    | sK11 != k3_tarski(k1_tarski(sK11))
    | sK11 = k3_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13074])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f158])).

cnf(c_3099,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK11))
    | X0 = sK11 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_6818,plain,
    ( ~ r2_hidden(sK8(k1_tarski(sK11),sK11),k1_tarski(sK11))
    | sK8(k1_tarski(sK11),sK11) = sK11 ),
    inference(instantiation,[status(thm)],[c_3099])).

cnf(c_6833,plain,
    ( sK8(k1_tarski(sK11),sK11) = sK11
    | r2_hidden(sK8(k1_tarski(sK11),sK11),k1_tarski(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6818])).

cnf(c_3492,plain,
    ( ~ r2_hidden(sK7(k1_tarski(sK11),sK11),k1_tarski(X0))
    | sK7(k1_tarski(sK11),sK11) = X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4861,plain,
    ( ~ r2_hidden(sK7(k1_tarski(sK11),sK11),k1_tarski(sK7(k1_tarski(sK11),sK11)))
    | sK7(k1_tarski(sK11),sK11) = sK7(k1_tarski(sK11),sK11) ),
    inference(instantiation,[status(thm)],[c_3492])).

cnf(c_39,plain,
    ( k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_4306,plain,
    ( k3_tarski(k1_tarski(sK11)) = sK11 ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_4259,plain,
    ( X0 != k1_tarski(sK11)
    | k1_tarski(sK11) = X0
    | k1_tarski(sK11) != k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_4260,plain,
    ( k1_tarski(sK11) != k1_tarski(sK11)
    | k1_tarski(sK11) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_4259])).

cnf(c_22,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_3876,plain,
    ( r2_hidden(sK7(k1_tarski(sK11),sK11),k1_tarski(sK7(k1_tarski(sK11),sK11))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3665,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK11,k1_tarski(sK11))
    | X1 != k1_tarski(sK11)
    | X0 != sK11 ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_3667,plain,
    ( ~ r2_hidden(sK11,k1_tarski(sK11))
    | r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_tarski(sK11)
    | k1_xboole_0 != sK11 ),
    inference(instantiation,[status(thm)],[c_3665])).

cnf(c_3630,plain,
    ( k3_tarski(X0) != X1
    | k1_tarski(sK11) != X1
    | k1_tarski(sK11) = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_2494])).

cnf(c_3651,plain,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0
    | k1_tarski(sK11) = k3_tarski(k1_xboole_0)
    | k1_tarski(sK11) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3630])).

cnf(c_2552,plain,
    ( X0 != sK11
    | sK11 = X0
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_3108,plain,
    ( k3_tarski(k1_tarski(sK11)) != sK11
    | sK11 = k3_tarski(k1_tarski(sK11))
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_3081,plain,
    ( k1_tarski(sK11) != sK11
    | sK11 = k1_tarski(sK11)
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_1102,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3072,plain,
    ( k1_tarski(sK11) = k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_2217,plain,
    ( ~ r2_hidden(sK11,k1_tarski(X0))
    | sK11 = X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2431,plain,
    ( ~ r2_hidden(sK11,k1_tarski(sK11))
    | sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_2291,plain,
    ( r2_hidden(sK11,k1_tarski(sK11)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2292,plain,
    ( r2_hidden(sK11,k1_tarski(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2291])).

cnf(c_50,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK7(X1,X2),X2)
    | r2_hidden(sK7(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2126,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK11))
    | r2_hidden(sK7(k1_tarski(sK11),sK11),X0)
    | r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
    | k1_setfam_1(k1_tarski(sK11)) = sK11
    | k1_xboole_0 = k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_2201,plain,
    ( r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
    | ~ r2_hidden(sK11,k1_tarski(sK11))
    | k1_setfam_1(k1_tarski(sK11)) = sK11
    | k1_xboole_0 = k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_2202,plain,
    ( k1_setfam_1(k1_tarski(sK11)) = sK11
    | k1_xboole_0 = k1_tarski(sK11)
    | r2_hidden(sK7(k1_tarski(sK11),sK11),sK11) = iProver_top
    | r2_hidden(sK11,k1_tarski(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2201])).

cnf(c_48,plain,
    ( ~ r2_hidden(sK7(X0,X1),X1)
    | ~ r2_hidden(sK7(X0,X1),sK8(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2120,plain,
    ( ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK8(k1_tarski(sK11),sK11))
    | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
    | k1_setfam_1(k1_tarski(sK11)) = sK11
    | k1_xboole_0 = k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_49,plain,
    ( r2_hidden(sK8(X0,X1),X0)
    | ~ r2_hidden(sK7(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_2121,plain,
    ( r2_hidden(sK8(k1_tarski(sK11),sK11),k1_tarski(sK11))
    | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
    | k1_setfam_1(k1_tarski(sK11)) = sK11
    | k1_xboole_0 = k1_tarski(sK11) ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_2122,plain,
    ( k1_setfam_1(k1_tarski(sK11)) = sK11
    | k1_xboole_0 = k1_tarski(sK11)
    | r2_hidden(sK8(k1_tarski(sK11),sK11),k1_tarski(sK11)) = iProver_top
    | r2_hidden(sK7(k1_tarski(sK11),sK11),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2121])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_190,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_38,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_60,negated_conjecture,
    ( k1_setfam_1(k1_tarski(sK11)) != sK11 ),
    inference(cnf_transformation,[],[f149])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54242,c_36710,c_31101,c_13994,c_13075,c_6833,c_4861,c_4306,c_4260,c_3876,c_3667,c_3651,c_3108,c_3081,c_3072,c_2431,c_2292,c_2291,c_2202,c_2201,c_2120,c_2122,c_190,c_38,c_60])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.05/3.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.05/3.01  
% 19.05/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.05/3.01  
% 19.05/3.01  ------  iProver source info
% 19.05/3.01  
% 19.05/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.05/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.05/3.01  git: non_committed_changes: false
% 19.05/3.01  git: last_make_outside_of_git: false
% 19.05/3.01  
% 19.05/3.01  ------ 
% 19.05/3.01  
% 19.05/3.01  ------ Input Options
% 19.05/3.01  
% 19.05/3.01  --out_options                           all
% 19.05/3.01  --tptp_safe_out                         true
% 19.05/3.01  --problem_path                          ""
% 19.05/3.01  --include_path                          ""
% 19.05/3.01  --clausifier                            res/vclausify_rel
% 19.05/3.01  --clausifier_options                    ""
% 19.05/3.01  --stdin                                 false
% 19.05/3.01  --stats_out                             all
% 19.05/3.01  
% 19.05/3.01  ------ General Options
% 19.05/3.01  
% 19.05/3.01  --fof                                   false
% 19.05/3.01  --time_out_real                         305.
% 19.05/3.01  --time_out_virtual                      -1.
% 19.05/3.01  --symbol_type_check                     false
% 19.05/3.01  --clausify_out                          false
% 19.05/3.01  --sig_cnt_out                           false
% 19.05/3.01  --trig_cnt_out                          false
% 19.05/3.01  --trig_cnt_out_tolerance                1.
% 19.05/3.01  --trig_cnt_out_sk_spl                   false
% 19.05/3.01  --abstr_cl_out                          false
% 19.05/3.01  
% 19.05/3.01  ------ Global Options
% 19.05/3.01  
% 19.05/3.01  --schedule                              default
% 19.05/3.01  --add_important_lit                     false
% 19.05/3.01  --prop_solver_per_cl                    1000
% 19.05/3.01  --min_unsat_core                        false
% 19.05/3.01  --soft_assumptions                      false
% 19.05/3.01  --soft_lemma_size                       3
% 19.05/3.01  --prop_impl_unit_size                   0
% 19.05/3.01  --prop_impl_unit                        []
% 19.05/3.01  --share_sel_clauses                     true
% 19.05/3.01  --reset_solvers                         false
% 19.05/3.01  --bc_imp_inh                            [conj_cone]
% 19.05/3.01  --conj_cone_tolerance                   3.
% 19.05/3.01  --extra_neg_conj                        none
% 19.05/3.01  --large_theory_mode                     true
% 19.05/3.01  --prolific_symb_bound                   200
% 19.05/3.01  --lt_threshold                          2000
% 19.05/3.01  --clause_weak_htbl                      true
% 19.05/3.01  --gc_record_bc_elim                     false
% 19.05/3.01  
% 19.05/3.01  ------ Preprocessing Options
% 19.05/3.01  
% 19.05/3.01  --preprocessing_flag                    true
% 19.05/3.01  --time_out_prep_mult                    0.1
% 19.05/3.01  --splitting_mode                        input
% 19.05/3.01  --splitting_grd                         true
% 19.05/3.01  --splitting_cvd                         false
% 19.05/3.01  --splitting_cvd_svl                     false
% 19.05/3.01  --splitting_nvd                         32
% 19.05/3.01  --sub_typing                            true
% 19.05/3.01  --prep_gs_sim                           true
% 19.05/3.01  --prep_unflatten                        true
% 19.05/3.01  --prep_res_sim                          true
% 19.05/3.01  --prep_upred                            true
% 19.05/3.01  --prep_sem_filter                       exhaustive
% 19.05/3.01  --prep_sem_filter_out                   false
% 19.05/3.01  --pred_elim                             true
% 19.05/3.01  --res_sim_input                         true
% 19.05/3.01  --eq_ax_congr_red                       true
% 19.05/3.01  --pure_diseq_elim                       true
% 19.05/3.01  --brand_transform                       false
% 19.05/3.01  --non_eq_to_eq                          false
% 19.05/3.01  --prep_def_merge                        true
% 19.05/3.01  --prep_def_merge_prop_impl              false
% 19.05/3.01  --prep_def_merge_mbd                    true
% 19.05/3.01  --prep_def_merge_tr_red                 false
% 19.05/3.01  --prep_def_merge_tr_cl                  false
% 19.05/3.01  --smt_preprocessing                     true
% 19.05/3.01  --smt_ac_axioms                         fast
% 19.05/3.01  --preprocessed_out                      false
% 19.05/3.01  --preprocessed_stats                    false
% 19.05/3.01  
% 19.05/3.01  ------ Abstraction refinement Options
% 19.05/3.01  
% 19.05/3.01  --abstr_ref                             []
% 19.05/3.01  --abstr_ref_prep                        false
% 19.05/3.01  --abstr_ref_until_sat                   false
% 19.05/3.01  --abstr_ref_sig_restrict                funpre
% 19.05/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.05/3.01  --abstr_ref_under                       []
% 19.05/3.01  
% 19.05/3.01  ------ SAT Options
% 19.05/3.01  
% 19.05/3.01  --sat_mode                              false
% 19.05/3.01  --sat_fm_restart_options                ""
% 19.05/3.01  --sat_gr_def                            false
% 19.05/3.01  --sat_epr_types                         true
% 19.05/3.01  --sat_non_cyclic_types                  false
% 19.05/3.01  --sat_finite_models                     false
% 19.05/3.01  --sat_fm_lemmas                         false
% 19.05/3.01  --sat_fm_prep                           false
% 19.05/3.01  --sat_fm_uc_incr                        true
% 19.05/3.01  --sat_out_model                         small
% 19.05/3.01  --sat_out_clauses                       false
% 19.05/3.01  
% 19.05/3.01  ------ QBF Options
% 19.05/3.01  
% 19.05/3.01  --qbf_mode                              false
% 19.05/3.01  --qbf_elim_univ                         false
% 19.05/3.01  --qbf_dom_inst                          none
% 19.05/3.01  --qbf_dom_pre_inst                      false
% 19.05/3.01  --qbf_sk_in                             false
% 19.05/3.01  --qbf_pred_elim                         true
% 19.05/3.01  --qbf_split                             512
% 19.05/3.01  
% 19.05/3.01  ------ BMC1 Options
% 19.05/3.01  
% 19.05/3.01  --bmc1_incremental                      false
% 19.05/3.01  --bmc1_axioms                           reachable_all
% 19.05/3.01  --bmc1_min_bound                        0
% 19.05/3.01  --bmc1_max_bound                        -1
% 19.05/3.01  --bmc1_max_bound_default                -1
% 19.05/3.01  --bmc1_symbol_reachability              true
% 19.05/3.01  --bmc1_property_lemmas                  false
% 19.05/3.01  --bmc1_k_induction                      false
% 19.05/3.01  --bmc1_non_equiv_states                 false
% 19.05/3.01  --bmc1_deadlock                         false
% 19.05/3.01  --bmc1_ucm                              false
% 19.05/3.01  --bmc1_add_unsat_core                   none
% 19.05/3.01  --bmc1_unsat_core_children              false
% 19.05/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.05/3.01  --bmc1_out_stat                         full
% 19.05/3.01  --bmc1_ground_init                      false
% 19.05/3.01  --bmc1_pre_inst_next_state              false
% 19.05/3.01  --bmc1_pre_inst_state                   false
% 19.05/3.01  --bmc1_pre_inst_reach_state             false
% 19.05/3.01  --bmc1_out_unsat_core                   false
% 19.05/3.01  --bmc1_aig_witness_out                  false
% 19.05/3.01  --bmc1_verbose                          false
% 19.05/3.01  --bmc1_dump_clauses_tptp                false
% 19.05/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.05/3.01  --bmc1_dump_file                        -
% 19.05/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.05/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.05/3.01  --bmc1_ucm_extend_mode                  1
% 19.05/3.01  --bmc1_ucm_init_mode                    2
% 19.05/3.01  --bmc1_ucm_cone_mode                    none
% 19.05/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.05/3.01  --bmc1_ucm_relax_model                  4
% 19.05/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.05/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.05/3.01  --bmc1_ucm_layered_model                none
% 19.05/3.01  --bmc1_ucm_max_lemma_size               10
% 19.05/3.01  
% 19.05/3.01  ------ AIG Options
% 19.05/3.01  
% 19.05/3.01  --aig_mode                              false
% 19.05/3.01  
% 19.05/3.01  ------ Instantiation Options
% 19.05/3.01  
% 19.05/3.01  --instantiation_flag                    true
% 19.05/3.01  --inst_sos_flag                         true
% 19.05/3.01  --inst_sos_phase                        true
% 19.05/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.05/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.05/3.01  --inst_lit_sel_side                     num_symb
% 19.05/3.01  --inst_solver_per_active                1400
% 19.05/3.01  --inst_solver_calls_frac                1.
% 19.05/3.01  --inst_passive_queue_type               priority_queues
% 19.05/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.05/3.01  --inst_passive_queues_freq              [25;2]
% 19.05/3.01  --inst_dismatching                      true
% 19.05/3.01  --inst_eager_unprocessed_to_passive     true
% 19.05/3.01  --inst_prop_sim_given                   true
% 19.05/3.01  --inst_prop_sim_new                     false
% 19.05/3.01  --inst_subs_new                         false
% 19.05/3.01  --inst_eq_res_simp                      false
% 19.05/3.01  --inst_subs_given                       false
% 19.05/3.01  --inst_orphan_elimination               true
% 19.05/3.01  --inst_learning_loop_flag               true
% 19.05/3.01  --inst_learning_start                   3000
% 19.05/3.01  --inst_learning_factor                  2
% 19.05/3.01  --inst_start_prop_sim_after_learn       3
% 19.05/3.01  --inst_sel_renew                        solver
% 19.05/3.01  --inst_lit_activity_flag                true
% 19.05/3.01  --inst_restr_to_given                   false
% 19.05/3.01  --inst_activity_threshold               500
% 19.05/3.01  --inst_out_proof                        true
% 19.05/3.01  
% 19.05/3.01  ------ Resolution Options
% 19.05/3.01  
% 19.05/3.01  --resolution_flag                       true
% 19.05/3.01  --res_lit_sel                           adaptive
% 19.05/3.01  --res_lit_sel_side                      none
% 19.05/3.01  --res_ordering                          kbo
% 19.05/3.01  --res_to_prop_solver                    active
% 19.05/3.01  --res_prop_simpl_new                    false
% 19.05/3.01  --res_prop_simpl_given                  true
% 19.05/3.01  --res_passive_queue_type                priority_queues
% 19.05/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.05/3.01  --res_passive_queues_freq               [15;5]
% 19.05/3.01  --res_forward_subs                      full
% 19.05/3.01  --res_backward_subs                     full
% 19.05/3.01  --res_forward_subs_resolution           true
% 19.05/3.01  --res_backward_subs_resolution          true
% 19.05/3.01  --res_orphan_elimination                true
% 19.05/3.01  --res_time_limit                        2.
% 19.05/3.01  --res_out_proof                         true
% 19.05/3.01  
% 19.05/3.01  ------ Superposition Options
% 19.05/3.01  
% 19.05/3.01  --superposition_flag                    true
% 19.05/3.01  --sup_passive_queue_type                priority_queues
% 19.05/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.05/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.05/3.01  --demod_completeness_check              fast
% 19.05/3.01  --demod_use_ground                      true
% 19.05/3.01  --sup_to_prop_solver                    passive
% 19.05/3.01  --sup_prop_simpl_new                    true
% 19.05/3.01  --sup_prop_simpl_given                  true
% 19.05/3.01  --sup_fun_splitting                     true
% 19.05/3.01  --sup_smt_interval                      50000
% 19.05/3.01  
% 19.05/3.01  ------ Superposition Simplification Setup
% 19.05/3.01  
% 19.05/3.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.05/3.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.05/3.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.05/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.05/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.05/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.05/3.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.05/3.01  --sup_immed_triv                        [TrivRules]
% 19.05/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.05/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.05/3.01  --sup_immed_bw_main                     []
% 19.05/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.05/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.05/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.05/3.01  --sup_input_bw                          []
% 19.05/3.01  
% 19.05/3.01  ------ Combination Options
% 19.05/3.01  
% 19.05/3.01  --comb_res_mult                         3
% 19.05/3.01  --comb_sup_mult                         2
% 19.05/3.01  --comb_inst_mult                        10
% 19.05/3.01  
% 19.05/3.01  ------ Debug Options
% 19.05/3.01  
% 19.05/3.01  --dbg_backtrace                         false
% 19.05/3.01  --dbg_dump_prop_clauses                 false
% 19.05/3.01  --dbg_dump_prop_clauses_file            -
% 19.05/3.01  --dbg_out_stat                          false
% 19.05/3.01  ------ Parsing...
% 19.05/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.05/3.01  
% 19.05/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.05/3.01  
% 19.05/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.05/3.01  
% 19.05/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.05/3.01  ------ Proving...
% 19.05/3.01  ------ Problem Properties 
% 19.05/3.01  
% 19.05/3.01  
% 19.05/3.01  clauses                                 56
% 19.05/3.01  conjectures                             1
% 19.05/3.01  EPR                                     5
% 19.05/3.01  Horn                                    42
% 19.05/3.01  unary                                   16
% 19.05/3.01  binary                                  19
% 19.05/3.01  lits                                    124
% 19.05/3.01  lits eq                                 39
% 19.05/3.01  fd_pure                                 0
% 19.05/3.01  fd_pseudo                               0
% 19.05/3.01  fd_cond                                 7
% 19.05/3.01  fd_pseudo_cond                          12
% 19.05/3.01  AC symbols                              0
% 19.05/3.01  
% 19.05/3.01  ------ Schedule dynamic 5 is on 
% 19.05/3.01  
% 19.05/3.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.05/3.01  
% 19.05/3.01  
% 19.05/3.01  ------ 
% 19.05/3.01  Current options:
% 19.05/3.01  ------ 
% 19.05/3.01  
% 19.05/3.01  ------ Input Options
% 19.05/3.01  
% 19.05/3.01  --out_options                           all
% 19.05/3.01  --tptp_safe_out                         true
% 19.05/3.01  --problem_path                          ""
% 19.05/3.01  --include_path                          ""
% 19.05/3.01  --clausifier                            res/vclausify_rel
% 19.05/3.01  --clausifier_options                    ""
% 19.05/3.01  --stdin                                 false
% 19.05/3.01  --stats_out                             all
% 19.05/3.01  
% 19.05/3.01  ------ General Options
% 19.05/3.01  
% 19.05/3.01  --fof                                   false
% 19.05/3.01  --time_out_real                         305.
% 19.05/3.01  --time_out_virtual                      -1.
% 19.05/3.01  --symbol_type_check                     false
% 19.05/3.01  --clausify_out                          false
% 19.05/3.01  --sig_cnt_out                           false
% 19.05/3.01  --trig_cnt_out                          false
% 19.05/3.01  --trig_cnt_out_tolerance                1.
% 19.05/3.01  --trig_cnt_out_sk_spl                   false
% 19.05/3.01  --abstr_cl_out                          false
% 19.05/3.01  
% 19.05/3.01  ------ Global Options
% 19.05/3.01  
% 19.05/3.01  --schedule                              default
% 19.05/3.01  --add_important_lit                     false
% 19.05/3.01  --prop_solver_per_cl                    1000
% 19.05/3.01  --min_unsat_core                        false
% 19.05/3.01  --soft_assumptions                      false
% 19.05/3.01  --soft_lemma_size                       3
% 19.05/3.01  --prop_impl_unit_size                   0
% 19.05/3.01  --prop_impl_unit                        []
% 19.05/3.01  --share_sel_clauses                     true
% 19.05/3.01  --reset_solvers                         false
% 19.05/3.01  --bc_imp_inh                            [conj_cone]
% 19.05/3.01  --conj_cone_tolerance                   3.
% 19.05/3.01  --extra_neg_conj                        none
% 19.05/3.01  --large_theory_mode                     true
% 19.05/3.01  --prolific_symb_bound                   200
% 19.05/3.01  --lt_threshold                          2000
% 19.05/3.01  --clause_weak_htbl                      true
% 19.05/3.01  --gc_record_bc_elim                     false
% 19.05/3.01  
% 19.05/3.01  ------ Preprocessing Options
% 19.05/3.01  
% 19.05/3.01  --preprocessing_flag                    true
% 19.05/3.01  --time_out_prep_mult                    0.1
% 19.05/3.01  --splitting_mode                        input
% 19.05/3.01  --splitting_grd                         true
% 19.05/3.01  --splitting_cvd                         false
% 19.05/3.01  --splitting_cvd_svl                     false
% 19.05/3.01  --splitting_nvd                         32
% 19.05/3.01  --sub_typing                            true
% 19.05/3.01  --prep_gs_sim                           true
% 19.05/3.01  --prep_unflatten                        true
% 19.05/3.01  --prep_res_sim                          true
% 19.05/3.01  --prep_upred                            true
% 19.05/3.01  --prep_sem_filter                       exhaustive
% 19.05/3.01  --prep_sem_filter_out                   false
% 19.05/3.01  --pred_elim                             true
% 19.05/3.01  --res_sim_input                         true
% 19.05/3.01  --eq_ax_congr_red                       true
% 19.05/3.01  --pure_diseq_elim                       true
% 19.05/3.01  --brand_transform                       false
% 19.05/3.01  --non_eq_to_eq                          false
% 19.05/3.01  --prep_def_merge                        true
% 19.05/3.01  --prep_def_merge_prop_impl              false
% 19.05/3.01  --prep_def_merge_mbd                    true
% 19.05/3.01  --prep_def_merge_tr_red                 false
% 19.05/3.01  --prep_def_merge_tr_cl                  false
% 19.05/3.01  --smt_preprocessing                     true
% 19.05/3.01  --smt_ac_axioms                         fast
% 19.05/3.01  --preprocessed_out                      false
% 19.05/3.01  --preprocessed_stats                    false
% 19.05/3.01  
% 19.05/3.01  ------ Abstraction refinement Options
% 19.05/3.01  
% 19.05/3.01  --abstr_ref                             []
% 19.05/3.01  --abstr_ref_prep                        false
% 19.05/3.01  --abstr_ref_until_sat                   false
% 19.05/3.01  --abstr_ref_sig_restrict                funpre
% 19.05/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.05/3.01  --abstr_ref_under                       []
% 19.05/3.01  
% 19.05/3.01  ------ SAT Options
% 19.05/3.01  
% 19.05/3.01  --sat_mode                              false
% 19.05/3.01  --sat_fm_restart_options                ""
% 19.05/3.01  --sat_gr_def                            false
% 19.05/3.01  --sat_epr_types                         true
% 19.05/3.01  --sat_non_cyclic_types                  false
% 19.05/3.01  --sat_finite_models                     false
% 19.05/3.01  --sat_fm_lemmas                         false
% 19.05/3.01  --sat_fm_prep                           false
% 19.05/3.01  --sat_fm_uc_incr                        true
% 19.05/3.01  --sat_out_model                         small
% 19.05/3.01  --sat_out_clauses                       false
% 19.05/3.01  
% 19.05/3.01  ------ QBF Options
% 19.05/3.01  
% 19.05/3.01  --qbf_mode                              false
% 19.05/3.01  --qbf_elim_univ                         false
% 19.05/3.01  --qbf_dom_inst                          none
% 19.05/3.01  --qbf_dom_pre_inst                      false
% 19.05/3.01  --qbf_sk_in                             false
% 19.05/3.01  --qbf_pred_elim                         true
% 19.05/3.01  --qbf_split                             512
% 19.05/3.01  
% 19.05/3.01  ------ BMC1 Options
% 19.05/3.01  
% 19.05/3.01  --bmc1_incremental                      false
% 19.05/3.01  --bmc1_axioms                           reachable_all
% 19.05/3.01  --bmc1_min_bound                        0
% 19.05/3.01  --bmc1_max_bound                        -1
% 19.05/3.01  --bmc1_max_bound_default                -1
% 19.05/3.01  --bmc1_symbol_reachability              true
% 19.05/3.01  --bmc1_property_lemmas                  false
% 19.05/3.01  --bmc1_k_induction                      false
% 19.05/3.01  --bmc1_non_equiv_states                 false
% 19.05/3.01  --bmc1_deadlock                         false
% 19.05/3.01  --bmc1_ucm                              false
% 19.05/3.01  --bmc1_add_unsat_core                   none
% 19.05/3.01  --bmc1_unsat_core_children              false
% 19.05/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.05/3.01  --bmc1_out_stat                         full
% 19.05/3.01  --bmc1_ground_init                      false
% 19.05/3.01  --bmc1_pre_inst_next_state              false
% 19.05/3.01  --bmc1_pre_inst_state                   false
% 19.05/3.01  --bmc1_pre_inst_reach_state             false
% 19.05/3.01  --bmc1_out_unsat_core                   false
% 19.05/3.01  --bmc1_aig_witness_out                  false
% 19.05/3.01  --bmc1_verbose                          false
% 19.05/3.01  --bmc1_dump_clauses_tptp                false
% 19.05/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.05/3.01  --bmc1_dump_file                        -
% 19.05/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.05/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.05/3.01  --bmc1_ucm_extend_mode                  1
% 19.05/3.01  --bmc1_ucm_init_mode                    2
% 19.05/3.01  --bmc1_ucm_cone_mode                    none
% 19.05/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.05/3.01  --bmc1_ucm_relax_model                  4
% 19.05/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.05/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.05/3.01  --bmc1_ucm_layered_model                none
% 19.05/3.01  --bmc1_ucm_max_lemma_size               10
% 19.05/3.01  
% 19.05/3.01  ------ AIG Options
% 19.05/3.01  
% 19.05/3.01  --aig_mode                              false
% 19.05/3.01  
% 19.05/3.01  ------ Instantiation Options
% 19.05/3.01  
% 19.05/3.01  --instantiation_flag                    true
% 19.05/3.01  --inst_sos_flag                         true
% 19.05/3.01  --inst_sos_phase                        true
% 19.05/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.05/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.05/3.01  --inst_lit_sel_side                     none
% 19.05/3.01  --inst_solver_per_active                1400
% 19.05/3.01  --inst_solver_calls_frac                1.
% 19.05/3.01  --inst_passive_queue_type               priority_queues
% 19.05/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.05/3.01  --inst_passive_queues_freq              [25;2]
% 19.05/3.01  --inst_dismatching                      true
% 19.05/3.01  --inst_eager_unprocessed_to_passive     true
% 19.05/3.01  --inst_prop_sim_given                   true
% 19.05/3.01  --inst_prop_sim_new                     false
% 19.05/3.01  --inst_subs_new                         false
% 19.05/3.01  --inst_eq_res_simp                      false
% 19.05/3.01  --inst_subs_given                       false
% 19.05/3.01  --inst_orphan_elimination               true
% 19.05/3.01  --inst_learning_loop_flag               true
% 19.05/3.01  --inst_learning_start                   3000
% 19.05/3.01  --inst_learning_factor                  2
% 19.05/3.01  --inst_start_prop_sim_after_learn       3
% 19.05/3.01  --inst_sel_renew                        solver
% 19.05/3.01  --inst_lit_activity_flag                true
% 19.05/3.01  --inst_restr_to_given                   false
% 19.05/3.01  --inst_activity_threshold               500
% 19.05/3.01  --inst_out_proof                        true
% 19.05/3.01  
% 19.05/3.01  ------ Resolution Options
% 19.05/3.01  
% 19.05/3.01  --resolution_flag                       false
% 19.05/3.01  --res_lit_sel                           adaptive
% 19.05/3.01  --res_lit_sel_side                      none
% 19.05/3.01  --res_ordering                          kbo
% 19.05/3.01  --res_to_prop_solver                    active
% 19.05/3.01  --res_prop_simpl_new                    false
% 19.05/3.01  --res_prop_simpl_given                  true
% 19.05/3.01  --res_passive_queue_type                priority_queues
% 19.05/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.05/3.01  --res_passive_queues_freq               [15;5]
% 19.05/3.01  --res_forward_subs                      full
% 19.05/3.01  --res_backward_subs                     full
% 19.05/3.01  --res_forward_subs_resolution           true
% 19.05/3.01  --res_backward_subs_resolution          true
% 19.05/3.01  --res_orphan_elimination                true
% 19.05/3.01  --res_time_limit                        2.
% 19.05/3.01  --res_out_proof                         true
% 19.05/3.01  
% 19.05/3.01  ------ Superposition Options
% 19.05/3.01  
% 19.05/3.01  --superposition_flag                    true
% 19.05/3.01  --sup_passive_queue_type                priority_queues
% 19.05/3.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.05/3.01  --sup_passive_queues_freq               [8;1;4]
% 19.05/3.01  --demod_completeness_check              fast
% 19.05/3.01  --demod_use_ground                      true
% 19.05/3.01  --sup_to_prop_solver                    passive
% 19.05/3.01  --sup_prop_simpl_new                    true
% 19.05/3.01  --sup_prop_simpl_given                  true
% 19.05/3.01  --sup_fun_splitting                     true
% 19.05/3.01  --sup_smt_interval                      50000
% 19.05/3.01  
% 19.05/3.01  ------ Superposition Simplification Setup
% 19.05/3.01  
% 19.05/3.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.05/3.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.05/3.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.05/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.05/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.05/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.05/3.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.05/3.01  --sup_immed_triv                        [TrivRules]
% 19.05/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.05/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.05/3.01  --sup_immed_bw_main                     []
% 19.05/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.05/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.05/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.05/3.01  --sup_input_bw                          []
% 19.05/3.01  
% 19.05/3.01  ------ Combination Options
% 19.05/3.01  
% 19.05/3.01  --comb_res_mult                         3
% 19.05/3.01  --comb_sup_mult                         2
% 19.05/3.01  --comb_inst_mult                        10
% 19.05/3.01  
% 19.05/3.01  ------ Debug Options
% 19.05/3.01  
% 19.05/3.01  --dbg_backtrace                         false
% 19.05/3.01  --dbg_dump_prop_clauses                 false
% 19.05/3.01  --dbg_dump_prop_clauses_file            -
% 19.05/3.01  --dbg_out_stat                          false
% 19.05/3.01  
% 19.05/3.01  
% 19.05/3.01  
% 19.05/3.01  
% 19.05/3.01  ------ Proving...
% 19.05/3.01  
% 19.05/3.01  
% 19.05/3.01  % SZS status Theorem for theBenchmark.p
% 19.05/3.01  
% 19.05/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.05/3.01  
% 19.05/3.01  fof(f13,axiom,(
% 19.05/3.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 19.05/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.01  
% 19.05/3.01  fof(f61,plain,(
% 19.05/3.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 19.05/3.01    inference(nnf_transformation,[],[f13])).
% 19.05/3.01  
% 19.05/3.01  fof(f62,plain,(
% 19.05/3.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.05/3.01    inference(rectify,[],[f61])).
% 19.05/3.01  
% 19.05/3.01  fof(f63,plain,(
% 19.05/3.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 19.05/3.01    introduced(choice_axiom,[])).
% 19.05/3.01  
% 19.05/3.01  fof(f64,plain,(
% 19.05/3.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.05/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).
% 19.05/3.01  
% 19.05/3.01  fof(f109,plain,(
% 19.05/3.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 19.05/3.01    inference(cnf_transformation,[],[f64])).
% 19.05/3.01  
% 19.05/3.01  fof(f158,plain,(
% 19.05/3.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 19.05/3.01    inference(equality_resolution,[],[f109])).
% 19.05/3.01  
% 19.05/3.01  fof(f20,axiom,(
% 19.05/3.01    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 19.05/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.01  
% 19.05/3.01  fof(f128,plain,(
% 19.05/3.01    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 19.05/3.01    inference(cnf_transformation,[],[f20])).
% 19.05/3.01  
% 19.05/3.01  fof(f110,plain,(
% 19.05/3.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 19.05/3.01    inference(cnf_transformation,[],[f64])).
% 19.05/3.01  
% 19.05/3.01  fof(f156,plain,(
% 19.05/3.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 19.05/3.01    inference(equality_resolution,[],[f110])).
% 19.05/3.01  
% 19.05/3.01  fof(f157,plain,(
% 19.05/3.01    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 19.05/3.01    inference(equality_resolution,[],[f156])).
% 19.05/3.01  
% 19.05/3.01  fof(f26,axiom,(
% 19.05/3.01    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 19.05/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.01  
% 19.05/3.01  fof(f45,plain,(
% 19.05/3.01    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 19.05/3.01    inference(ennf_transformation,[],[f26])).
% 19.05/3.01  
% 19.05/3.01  fof(f79,plain,(
% 19.05/3.01    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~r2_hidden(X2,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 19.05/3.01    inference(nnf_transformation,[],[f45])).
% 19.05/3.01  
% 19.05/3.01  fof(f80,plain,(
% 19.05/3.01    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | ? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 19.05/3.01    inference(rectify,[],[f79])).
% 19.05/3.01  
% 19.05/3.01  fof(f83,plain,(
% 19.05/3.01    ! [X5,X0] : (? [X6] : (~r2_hidden(X5,X6) & r2_hidden(X6,X0)) => (~r2_hidden(X5,sK9(X0,X5)) & r2_hidden(sK9(X0,X5),X0)))),
% 19.05/3.01    introduced(choice_axiom,[])).
% 19.05/3.01  
% 19.05/3.01  fof(f82,plain,(
% 19.05/3.01    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) => (~r2_hidden(X2,sK8(X0,X1)) & r2_hidden(sK8(X0,X1),X0)))) )),
% 19.05/3.01    introduced(choice_axiom,[])).
% 19.05/3.01  
% 19.05/3.01  fof(f81,plain,(
% 19.05/3.01    ! [X1,X0] : (? [X2] : ((? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) & (! [X4] : (r2_hidden(X2,X4) | ~r2_hidden(X4,X0)) | r2_hidden(X2,X1))) => ((? [X3] : (~r2_hidden(sK7(X0,X1),X3) & r2_hidden(X3,X0)) | ~r2_hidden(sK7(X0,X1),X1)) & (! [X4] : (r2_hidden(sK7(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK7(X0,X1),X1))))),
% 19.05/3.01    introduced(choice_axiom,[])).
% 19.05/3.01  
% 19.05/3.01  fof(f84,plain,(
% 19.05/3.01    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (((k1_setfam_1(X0) = X1 | (((~r2_hidden(sK7(X0,X1),sK8(X0,X1)) & r2_hidden(sK8(X0,X1),X0)) | ~r2_hidden(sK7(X0,X1),X1)) & (! [X4] : (r2_hidden(sK7(X0,X1),X4) | ~r2_hidden(X4,X0)) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | (~r2_hidden(X5,sK9(X0,X5)) & r2_hidden(sK9(X0,X5),X0))) & (! [X7] : (r2_hidden(X5,X7) | ~r2_hidden(X7,X0)) | ~r2_hidden(X5,X1))) | k1_setfam_1(X0) != X1)) | k1_xboole_0 = X0))),
% 19.05/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f80,f83,f82,f81])).
% 19.05/3.01  
% 19.05/3.01  fof(f138,plain,(
% 19.05/3.01    ( ! [X4,X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK7(X0,X1),X4) | ~r2_hidden(X4,X0) | r2_hidden(sK7(X0,X1),X1) | k1_xboole_0 = X0) )),
% 19.05/3.01    inference(cnf_transformation,[],[f84])).
% 19.05/3.01  
% 19.05/3.01  fof(f140,plain,(
% 19.05/3.01    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | ~r2_hidden(sK7(X0,X1),sK8(X0,X1)) | ~r2_hidden(sK7(X0,X1),X1) | k1_xboole_0 = X0) )),
% 19.05/3.01    inference(cnf_transformation,[],[f84])).
% 19.05/3.01  
% 19.05/3.01  fof(f139,plain,(
% 19.05/3.01    ( ! [X0,X1] : (k1_setfam_1(X0) = X1 | r2_hidden(sK8(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1) | k1_xboole_0 = X0) )),
% 19.05/3.01    inference(cnf_transformation,[],[f84])).
% 19.05/3.01  
% 19.05/3.01  fof(f1,axiom,(
% 19.05/3.01    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 19.05/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.01  
% 19.05/3.01  fof(f35,plain,(
% 19.05/3.01    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 19.05/3.01    inference(ennf_transformation,[],[f1])).
% 19.05/3.01  
% 19.05/3.01  fof(f89,plain,(
% 19.05/3.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 19.05/3.01    inference(cnf_transformation,[],[f35])).
% 19.05/3.01  
% 19.05/3.01  fof(f19,axiom,(
% 19.05/3.01    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 19.05/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.01  
% 19.05/3.01  fof(f127,plain,(
% 19.05/3.01    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 19.05/3.01    inference(cnf_transformation,[],[f19])).
% 19.05/3.01  
% 19.05/3.01  fof(f32,conjecture,(
% 19.05/3.01    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 19.05/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.05/3.01  
% 19.05/3.01  fof(f33,negated_conjecture,(
% 19.05/3.01    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 19.05/3.01    inference(negated_conjecture,[],[f32])).
% 19.05/3.01  
% 19.05/3.01  fof(f51,plain,(
% 19.05/3.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 19.05/3.01    inference(ennf_transformation,[],[f33])).
% 19.05/3.01  
% 19.05/3.01  fof(f87,plain,(
% 19.05/3.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK11)) != sK11),
% 19.05/3.01    introduced(choice_axiom,[])).
% 19.05/3.01  
% 19.05/3.01  fof(f88,plain,(
% 19.05/3.01    k1_setfam_1(k1_tarski(sK11)) != sK11),
% 19.05/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f51,f87])).
% 19.05/3.01  
% 19.05/3.01  fof(f149,plain,(
% 19.05/3.01    k1_setfam_1(k1_tarski(sK11)) != sK11),
% 19.05/3.01    inference(cnf_transformation,[],[f88])).
% 19.05/3.01  
% 19.05/3.01  cnf(c_1104,plain,
% 19.05/3.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.05/3.01      theory(equality) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_6702,plain,
% 19.05/3.01      ( r2_hidden(X0,X1)
% 19.05/3.01      | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
% 19.05/3.01      | X0 != sK7(k1_tarski(sK11),sK11)
% 19.05/3.01      | X1 != sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_1104]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_13538,plain,
% 19.05/3.01      ( r2_hidden(X0,sK8(k1_tarski(sK11),sK11))
% 19.05/3.01      | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
% 19.05/3.01      | X0 != sK7(k1_tarski(sK11),sK11)
% 19.05/3.01      | sK8(k1_tarski(sK11),sK11) != sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_6702]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_54242,plain,
% 19.05/3.01      ( r2_hidden(sK7(k1_tarski(sK11),sK11),sK8(k1_tarski(sK11),sK11))
% 19.05/3.01      | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
% 19.05/3.01      | sK8(k1_tarski(sK11),sK11) != sK11
% 19.05/3.01      | sK7(k1_tarski(sK11),sK11) != sK7(k1_tarski(sK11),sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_13538]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_1103,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2494,plain,
% 19.05/3.01      ( X0 != X1 | k1_tarski(sK11) != X1 | k1_tarski(sK11) = X0 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_1103]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_4945,plain,
% 19.05/3.01      ( X0 != k3_tarski(X1)
% 19.05/3.01      | k1_tarski(sK11) = X0
% 19.05/3.01      | k1_tarski(sK11) != k3_tarski(X1) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2494]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_36709,plain,
% 19.05/3.01      ( k1_tarski(sK11) != k3_tarski(X0)
% 19.05/3.01      | k1_tarski(sK11) = sK11
% 19.05/3.01      | sK11 != k3_tarski(X0) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_4945]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_36710,plain,
% 19.05/3.01      ( k1_tarski(sK11) != k3_tarski(k1_xboole_0)
% 19.05/3.01      | k1_tarski(sK11) = sK11
% 19.05/3.01      | sK11 != k3_tarski(k1_xboole_0) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_36709]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_1109,plain,
% 19.05/3.01      ( X0 != X1 | k3_tarski(X0) = k3_tarski(X1) ),
% 19.05/3.01      theory(equality) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_31100,plain,
% 19.05/3.01      ( X0 != k1_tarski(sK11)
% 19.05/3.01      | k3_tarski(X0) = k3_tarski(k1_tarski(sK11)) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_1109]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_31101,plain,
% 19.05/3.01      ( k3_tarski(k1_xboole_0) = k3_tarski(k1_tarski(sK11))
% 19.05/3.01      | k1_xboole_0 != k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_31100]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3114,plain,
% 19.05/3.01      ( X0 != X1 | X0 = sK11 | sK11 != X1 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_1103]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_13971,plain,
% 19.05/3.01      ( X0 != k1_tarski(sK11) | X0 = sK11 | sK11 != k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_3114]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_13994,plain,
% 19.05/3.01      ( sK11 != k1_tarski(sK11)
% 19.05/3.01      | k1_xboole_0 != k1_tarski(sK11)
% 19.05/3.01      | k1_xboole_0 = sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_13971]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2223,plain,
% 19.05/3.01      ( X0 != X1 | sK11 != X1 | sK11 = X0 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_1103]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_10565,plain,
% 19.05/3.01      ( X0 != k3_tarski(k1_tarski(sK11))
% 19.05/3.01      | sK11 = X0
% 19.05/3.01      | sK11 != k3_tarski(k1_tarski(sK11)) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2223]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_13074,plain,
% 19.05/3.01      ( k3_tarski(X0) != k3_tarski(k1_tarski(sK11))
% 19.05/3.01      | sK11 = k3_tarski(X0)
% 19.05/3.01      | sK11 != k3_tarski(k1_tarski(sK11)) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_10565]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_13075,plain,
% 19.05/3.01      ( k3_tarski(k1_xboole_0) != k3_tarski(k1_tarski(sK11))
% 19.05/3.01      | sK11 != k3_tarski(k1_tarski(sK11))
% 19.05/3.01      | sK11 = k3_tarski(k1_xboole_0) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_13074]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_23,plain,
% 19.05/3.01      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 19.05/3.01      inference(cnf_transformation,[],[f158]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3099,plain,
% 19.05/3.01      ( ~ r2_hidden(X0,k1_tarski(sK11)) | X0 = sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_23]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_6818,plain,
% 19.05/3.01      ( ~ r2_hidden(sK8(k1_tarski(sK11),sK11),k1_tarski(sK11))
% 19.05/3.01      | sK8(k1_tarski(sK11),sK11) = sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_3099]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_6833,plain,
% 19.05/3.01      ( sK8(k1_tarski(sK11),sK11) = sK11
% 19.05/3.01      | r2_hidden(sK8(k1_tarski(sK11),sK11),k1_tarski(sK11)) != iProver_top ),
% 19.05/3.01      inference(predicate_to_equality,[status(thm)],[c_6818]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3492,plain,
% 19.05/3.01      ( ~ r2_hidden(sK7(k1_tarski(sK11),sK11),k1_tarski(X0))
% 19.05/3.01      | sK7(k1_tarski(sK11),sK11) = X0 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_23]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_4861,plain,
% 19.05/3.01      ( ~ r2_hidden(sK7(k1_tarski(sK11),sK11),k1_tarski(sK7(k1_tarski(sK11),sK11)))
% 19.05/3.01      | sK7(k1_tarski(sK11),sK11) = sK7(k1_tarski(sK11),sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_3492]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_39,plain,
% 19.05/3.01      ( k3_tarski(k1_tarski(X0)) = X0 ),
% 19.05/3.01      inference(cnf_transformation,[],[f128]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_4306,plain,
% 19.05/3.01      ( k3_tarski(k1_tarski(sK11)) = sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_39]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_4259,plain,
% 19.05/3.01      ( X0 != k1_tarski(sK11)
% 19.05/3.01      | k1_tarski(sK11) = X0
% 19.05/3.01      | k1_tarski(sK11) != k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2494]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_4260,plain,
% 19.05/3.01      ( k1_tarski(sK11) != k1_tarski(sK11)
% 19.05/3.01      | k1_tarski(sK11) = k1_xboole_0
% 19.05/3.01      | k1_xboole_0 != k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_4259]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_22,plain,
% 19.05/3.01      ( r2_hidden(X0,k1_tarski(X0)) ),
% 19.05/3.01      inference(cnf_transformation,[],[f157]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3876,plain,
% 19.05/3.01      ( r2_hidden(sK7(k1_tarski(sK11),sK11),k1_tarski(sK7(k1_tarski(sK11),sK11))) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_22]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3665,plain,
% 19.05/3.01      ( r2_hidden(X0,X1)
% 19.05/3.01      | ~ r2_hidden(sK11,k1_tarski(sK11))
% 19.05/3.01      | X1 != k1_tarski(sK11)
% 19.05/3.01      | X0 != sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_1104]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3667,plain,
% 19.05/3.01      ( ~ r2_hidden(sK11,k1_tarski(sK11))
% 19.05/3.01      | r2_hidden(k1_xboole_0,k1_xboole_0)
% 19.05/3.01      | k1_xboole_0 != k1_tarski(sK11)
% 19.05/3.01      | k1_xboole_0 != sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_3665]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3630,plain,
% 19.05/3.01      ( k3_tarski(X0) != X1
% 19.05/3.01      | k1_tarski(sK11) != X1
% 19.05/3.01      | k1_tarski(sK11) = k3_tarski(X0) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2494]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3651,plain,
% 19.05/3.01      ( k3_tarski(k1_xboole_0) != k1_xboole_0
% 19.05/3.01      | k1_tarski(sK11) = k3_tarski(k1_xboole_0)
% 19.05/3.01      | k1_tarski(sK11) != k1_xboole_0 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_3630]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2552,plain,
% 19.05/3.01      ( X0 != sK11 | sK11 = X0 | sK11 != sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2223]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3108,plain,
% 19.05/3.01      ( k3_tarski(k1_tarski(sK11)) != sK11
% 19.05/3.01      | sK11 = k3_tarski(k1_tarski(sK11))
% 19.05/3.01      | sK11 != sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2552]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3081,plain,
% 19.05/3.01      ( k1_tarski(sK11) != sK11 | sK11 = k1_tarski(sK11) | sK11 != sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2552]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_1102,plain,( X0 = X0 ),theory(equality) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_3072,plain,
% 19.05/3.01      ( k1_tarski(sK11) = k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_1102]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2217,plain,
% 19.05/3.01      ( ~ r2_hidden(sK11,k1_tarski(X0)) | sK11 = X0 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_23]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2431,plain,
% 19.05/3.01      ( ~ r2_hidden(sK11,k1_tarski(sK11)) | sK11 = sK11 ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2217]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2291,plain,
% 19.05/3.01      ( r2_hidden(sK11,k1_tarski(sK11)) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_22]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2292,plain,
% 19.05/3.01      ( r2_hidden(sK11,k1_tarski(sK11)) = iProver_top ),
% 19.05/3.01      inference(predicate_to_equality,[status(thm)],[c_2291]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_50,plain,
% 19.05/3.01      ( ~ r2_hidden(X0,X1)
% 19.05/3.01      | r2_hidden(sK7(X1,X2),X2)
% 19.05/3.01      | r2_hidden(sK7(X1,X2),X0)
% 19.05/3.01      | k1_setfam_1(X1) = X2
% 19.05/3.01      | k1_xboole_0 = X1 ),
% 19.05/3.01      inference(cnf_transformation,[],[f138]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2126,plain,
% 19.05/3.01      ( ~ r2_hidden(X0,k1_tarski(sK11))
% 19.05/3.01      | r2_hidden(sK7(k1_tarski(sK11),sK11),X0)
% 19.05/3.01      | r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
% 19.05/3.01      | k1_setfam_1(k1_tarski(sK11)) = sK11
% 19.05/3.01      | k1_xboole_0 = k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_50]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2201,plain,
% 19.05/3.01      ( r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
% 19.05/3.01      | ~ r2_hidden(sK11,k1_tarski(sK11))
% 19.05/3.01      | k1_setfam_1(k1_tarski(sK11)) = sK11
% 19.05/3.01      | k1_xboole_0 = k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_2126]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2202,plain,
% 19.05/3.01      ( k1_setfam_1(k1_tarski(sK11)) = sK11
% 19.05/3.01      | k1_xboole_0 = k1_tarski(sK11)
% 19.05/3.01      | r2_hidden(sK7(k1_tarski(sK11),sK11),sK11) = iProver_top
% 19.05/3.01      | r2_hidden(sK11,k1_tarski(sK11)) != iProver_top ),
% 19.05/3.01      inference(predicate_to_equality,[status(thm)],[c_2201]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_48,plain,
% 19.05/3.01      ( ~ r2_hidden(sK7(X0,X1),X1)
% 19.05/3.01      | ~ r2_hidden(sK7(X0,X1),sK8(X0,X1))
% 19.05/3.01      | k1_setfam_1(X0) = X1
% 19.05/3.01      | k1_xboole_0 = X0 ),
% 19.05/3.01      inference(cnf_transformation,[],[f140]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2120,plain,
% 19.05/3.01      ( ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK8(k1_tarski(sK11),sK11))
% 19.05/3.01      | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
% 19.05/3.01      | k1_setfam_1(k1_tarski(sK11)) = sK11
% 19.05/3.01      | k1_xboole_0 = k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_48]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_49,plain,
% 19.05/3.01      ( r2_hidden(sK8(X0,X1),X0)
% 19.05/3.01      | ~ r2_hidden(sK7(X0,X1),X1)
% 19.05/3.01      | k1_setfam_1(X0) = X1
% 19.05/3.01      | k1_xboole_0 = X0 ),
% 19.05/3.01      inference(cnf_transformation,[],[f139]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2121,plain,
% 19.05/3.01      ( r2_hidden(sK8(k1_tarski(sK11),sK11),k1_tarski(sK11))
% 19.05/3.01      | ~ r2_hidden(sK7(k1_tarski(sK11),sK11),sK11)
% 19.05/3.01      | k1_setfam_1(k1_tarski(sK11)) = sK11
% 19.05/3.01      | k1_xboole_0 = k1_tarski(sK11) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_49]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_2122,plain,
% 19.05/3.01      ( k1_setfam_1(k1_tarski(sK11)) = sK11
% 19.05/3.01      | k1_xboole_0 = k1_tarski(sK11)
% 19.05/3.01      | r2_hidden(sK8(k1_tarski(sK11),sK11),k1_tarski(sK11)) = iProver_top
% 19.05/3.01      | r2_hidden(sK7(k1_tarski(sK11),sK11),sK11) != iProver_top ),
% 19.05/3.01      inference(predicate_to_equality,[status(thm)],[c_2121]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_0,plain,
% 19.05/3.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 19.05/3.01      inference(cnf_transformation,[],[f89]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_190,plain,
% 19.05/3.01      ( ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
% 19.05/3.01      inference(instantiation,[status(thm)],[c_0]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_38,plain,
% 19.05/3.01      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 19.05/3.01      inference(cnf_transformation,[],[f127]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(c_60,negated_conjecture,
% 19.05/3.01      ( k1_setfam_1(k1_tarski(sK11)) != sK11 ),
% 19.05/3.01      inference(cnf_transformation,[],[f149]) ).
% 19.05/3.01  
% 19.05/3.01  cnf(contradiction,plain,
% 19.05/3.01      ( $false ),
% 19.05/3.01      inference(minisat,
% 19.05/3.01                [status(thm)],
% 19.05/3.01                [c_54242,c_36710,c_31101,c_13994,c_13075,c_6833,c_4861,
% 19.05/3.01                 c_4306,c_4260,c_3876,c_3667,c_3651,c_3108,c_3081,c_3072,
% 19.05/3.01                 c_2431,c_2292,c_2291,c_2202,c_2201,c_2120,c_2122,c_190,
% 19.05/3.01                 c_38,c_60]) ).
% 19.05/3.01  
% 19.05/3.01  
% 19.05/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.05/3.01  
% 19.05/3.01  ------                               Statistics
% 19.05/3.01  
% 19.05/3.01  ------ General
% 19.05/3.01  
% 19.05/3.01  abstr_ref_over_cycles:                  0
% 19.05/3.01  abstr_ref_under_cycles:                 0
% 19.05/3.01  gc_basic_clause_elim:                   0
% 19.05/3.01  forced_gc_time:                         0
% 19.05/3.01  parsing_time:                           0.01
% 19.05/3.01  unif_index_cands_time:                  0.
% 19.05/3.01  unif_index_add_time:                    0.
% 19.05/3.01  orderings_time:                         0.
% 19.05/3.01  out_proof_time:                         0.021
% 19.05/3.01  total_time:                             2.015
% 19.05/3.01  num_of_symbols:                         53
% 19.05/3.01  num_of_terms:                           56236
% 19.05/3.01  
% 19.05/3.01  ------ Preprocessing
% 19.05/3.01  
% 19.05/3.01  num_of_splits:                          0
% 19.05/3.01  num_of_split_atoms:                     0
% 19.05/3.01  num_of_reused_defs:                     0
% 19.05/3.01  num_eq_ax_congr_red:                    72
% 19.05/3.01  num_of_sem_filtered_clauses:            1
% 19.05/3.01  num_of_subtypes:                        0
% 19.05/3.01  monotx_restored_types:                  0
% 19.05/3.01  sat_num_of_epr_types:                   0
% 19.05/3.01  sat_num_of_non_cyclic_types:            0
% 19.05/3.01  sat_guarded_non_collapsed_types:        0
% 19.05/3.01  num_pure_diseq_elim:                    0
% 19.05/3.01  simp_replaced_by:                       0
% 19.05/3.01  res_preprocessed:                       245
% 19.05/3.01  prep_upred:                             0
% 19.05/3.01  prep_unflattend:                        3
% 19.05/3.01  smt_new_axioms:                         0
% 19.05/3.01  pred_elim_cands:                        2
% 19.05/3.01  pred_elim:                              1
% 19.05/3.01  pred_elim_cl:                           2
% 19.05/3.01  pred_elim_cycles:                       3
% 19.05/3.01  merged_defs:                            16
% 19.05/3.01  merged_defs_ncl:                        0
% 19.05/3.01  bin_hyper_res:                          16
% 19.05/3.01  prep_cycles:                            4
% 19.05/3.01  pred_elim_time:                         0.003
% 19.05/3.01  splitting_time:                         0.
% 19.05/3.01  sem_filter_time:                        0.
% 19.05/3.01  monotx_time:                            0.
% 19.05/3.01  subtype_inf_time:                       0.
% 19.05/3.01  
% 19.05/3.01  ------ Problem properties
% 19.05/3.01  
% 19.05/3.01  clauses:                                56
% 19.05/3.01  conjectures:                            1
% 19.05/3.01  epr:                                    5
% 19.05/3.01  horn:                                   42
% 19.05/3.01  ground:                                 4
% 19.05/3.01  unary:                                  16
% 19.05/3.01  binary:                                 19
% 19.05/3.01  lits:                                   124
% 19.05/3.01  lits_eq:                                39
% 19.05/3.01  fd_pure:                                0
% 19.05/3.01  fd_pseudo:                              0
% 19.05/3.01  fd_cond:                                7
% 19.05/3.01  fd_pseudo_cond:                         12
% 19.05/3.01  ac_symbols:                             0
% 19.05/3.01  
% 19.05/3.01  ------ Propositional Solver
% 19.05/3.01  
% 19.05/3.01  prop_solver_calls:                      32
% 19.05/3.01  prop_fast_solver_calls:                 1652
% 19.05/3.01  smt_solver_calls:                       0
% 19.05/3.01  smt_fast_solver_calls:                  0
% 19.05/3.01  prop_num_of_clauses:                    22907
% 19.05/3.01  prop_preprocess_simplified:             47213
% 19.05/3.01  prop_fo_subsumed:                       10
% 19.05/3.01  prop_solver_time:                       0.
% 19.05/3.01  smt_solver_time:                        0.
% 19.05/3.01  smt_fast_solver_time:                   0.
% 19.05/3.01  prop_fast_solver_time:                  0.
% 19.05/3.01  prop_unsat_core_time:                   0.004
% 19.05/3.01  
% 19.05/3.01  ------ QBF
% 19.05/3.01  
% 19.05/3.01  qbf_q_res:                              0
% 19.05/3.01  qbf_num_tautologies:                    0
% 19.05/3.01  qbf_prep_cycles:                        0
% 19.05/3.01  
% 19.05/3.01  ------ BMC1
% 19.05/3.01  
% 19.05/3.01  bmc1_current_bound:                     -1
% 19.05/3.01  bmc1_last_solved_bound:                 -1
% 19.05/3.01  bmc1_unsat_core_size:                   -1
% 19.05/3.01  bmc1_unsat_core_parents_size:           -1
% 19.05/3.01  bmc1_merge_next_fun:                    0
% 19.05/3.01  bmc1_unsat_core_clauses_time:           0.
% 19.05/3.01  
% 19.05/3.01  ------ Instantiation
% 19.05/3.01  
% 19.05/3.01  inst_num_of_clauses:                    5573
% 19.05/3.01  inst_num_in_passive:                    3945
% 19.05/3.01  inst_num_in_active:                     1322
% 19.05/3.01  inst_num_in_unprocessed:                309
% 19.05/3.01  inst_num_of_loops:                      1816
% 19.05/3.01  inst_num_of_learning_restarts:          0
% 19.05/3.01  inst_num_moves_active_passive:          492
% 19.05/3.01  inst_lit_activity:                      0
% 19.05/3.01  inst_lit_activity_moves:                0
% 19.05/3.01  inst_num_tautologies:                   0
% 19.05/3.01  inst_num_prop_implied:                  0
% 19.05/3.01  inst_num_existing_simplified:           0
% 19.05/3.01  inst_num_eq_res_simplified:             0
% 19.05/3.01  inst_num_child_elim:                    0
% 19.05/3.01  inst_num_of_dismatching_blockings:      4720
% 19.05/3.01  inst_num_of_non_proper_insts:           6585
% 19.05/3.01  inst_num_of_duplicates:                 0
% 19.05/3.01  inst_inst_num_from_inst_to_res:         0
% 19.05/3.01  inst_dismatching_checking_time:         0.
% 19.05/3.01  
% 19.05/3.01  ------ Resolution
% 19.05/3.01  
% 19.05/3.01  res_num_of_clauses:                     0
% 19.05/3.01  res_num_in_passive:                     0
% 19.05/3.01  res_num_in_active:                      0
% 19.05/3.01  res_num_of_loops:                       249
% 19.05/3.01  res_forward_subset_subsumed:            556
% 19.05/3.01  res_backward_subset_subsumed:           8
% 19.05/3.01  res_forward_subsumed:                   0
% 19.05/3.01  res_backward_subsumed:                  0
% 19.05/3.01  res_forward_subsumption_resolution:     0
% 19.05/3.01  res_backward_subsumption_resolution:    0
% 19.05/3.01  res_clause_to_clause_subsumption:       6625
% 19.05/3.01  res_orphan_elimination:                 0
% 19.05/3.01  res_tautology_del:                      317
% 19.05/3.01  res_num_eq_res_simplified:              0
% 19.05/3.01  res_num_sel_changes:                    0
% 19.05/3.01  res_moves_from_active_to_pass:          0
% 19.05/3.01  
% 19.05/3.01  ------ Superposition
% 19.05/3.01  
% 19.05/3.01  sup_time_total:                         0.
% 19.05/3.01  sup_time_generating:                    0.
% 19.05/3.01  sup_time_sim_full:                      0.
% 19.05/3.01  sup_time_sim_immed:                     0.
% 19.05/3.01  
% 19.05/3.01  sup_num_of_clauses:                     1334
% 19.05/3.01  sup_num_in_active:                      307
% 19.05/3.01  sup_num_in_passive:                     1027
% 19.05/3.01  sup_num_of_loops:                       362
% 19.05/3.01  sup_fw_superposition:                   2586
% 19.05/3.01  sup_bw_superposition:                   2157
% 19.05/3.01  sup_immediate_simplified:               1044
% 19.05/3.01  sup_given_eliminated:                   8
% 19.05/3.01  comparisons_done:                       0
% 19.05/3.01  comparisons_avoided:                    9
% 19.05/3.01  
% 19.05/3.01  ------ Simplifications
% 19.05/3.01  
% 19.05/3.01  
% 19.05/3.01  sim_fw_subset_subsumed:                 75
% 19.05/3.01  sim_bw_subset_subsumed:                 4
% 19.05/3.01  sim_fw_subsumed:                        244
% 19.05/3.01  sim_bw_subsumed:                        51
% 19.05/3.01  sim_fw_subsumption_res:                 0
% 19.05/3.01  sim_bw_subsumption_res:                 0
% 19.05/3.01  sim_tautology_del:                      103
% 19.05/3.01  sim_eq_tautology_del:                   121
% 19.05/3.01  sim_eq_res_simp:                        7
% 19.05/3.01  sim_fw_demodulated:                     187
% 19.05/3.01  sim_bw_demodulated:                     14
% 19.05/3.01  sim_light_normalised:                   646
% 19.05/3.01  sim_joinable_taut:                      0
% 19.05/3.01  sim_joinable_simp:                      0
% 19.05/3.01  sim_ac_normalised:                      0
% 19.05/3.01  sim_smt_subsumption:                    0
% 19.05/3.01  
%------------------------------------------------------------------------------

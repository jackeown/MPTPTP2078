%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:41 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 195 expanded)
%              Number of clauses        :   61 (  71 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  383 ( 821 expanded)
%              Number of equality atoms :   97 ( 101 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
     => ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7))
        & r1_tarski(X0,X1)
        & r1_tarski(X2,sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3))
          & r1_tarski(sK4,sK5)
          & r1_tarski(sK6,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f17,f28,f27])).

fof(f46,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK1(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
                    & r2_hidden(sK1(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_455,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_469,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_958,plain,
    ( k3_xboole_0(sK4,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_455,c_469])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_452,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k3_xboole_0(X1,X2),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_458,plain,
    ( k8_relat_1(k3_xboole_0(X0,X1),X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1096,plain,
    ( k8_relat_1(X0,k8_relat_1(X1,sK6)) = k8_relat_1(k3_xboole_0(X0,X1),sK6) ),
    inference(superposition,[status(thm)],[c_452,c_458])).

cnf(c_1851,plain,
    ( k8_relat_1(sK4,k8_relat_1(sK5,sK6)) = k8_relat_1(sK4,sK6) ),
    inference(superposition,[status(thm)],[c_958,c_1096])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_461,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_464,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k8_relat_1(X3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_459,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_532,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_464,c_459])).

cnf(c_2031,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),X1) = iProver_top
    | r1_tarski(k8_relat_1(X0,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k8_relat_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_532])).

cnf(c_8831,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),X1) = iProver_top
    | r1_tarski(k8_relat_1(X0,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2031,c_459])).

cnf(c_7,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_462,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8854,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k8_relat_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8831,c_462])).

cnf(c_8981,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8854,c_459])).

cnf(c_13043,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) = iProver_top
    | v1_relat_1(k8_relat_1(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1851,c_8981])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X0,X1),X3)
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_677,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X2)
    | ~ r1_tarski(X0,X2)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_774,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),k8_relat_1(X2,X3))
    | ~ r1_tarski(X0,k8_relat_1(X2,X3))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1146,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),k8_relat_1(X0,X1))
    | r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),k8_relat_1(X3,X4))
    | ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X3,X4))
    | ~ v1_relat_1(k8_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_2239,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X0,X1))
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
    | ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(X0,X1))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_10488,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,X0))
    | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
    | ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_10489,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,X0)) = iProver_top
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6)) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0)) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10488])).

cnf(c_10491,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK6)) = iProver_top
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6)) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) != iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10489])).

cnf(c_785,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X2)
    | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X3)
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2252,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),X3)
    | r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),X4)
    | ~ r1_tarski(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_5305,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0)
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
    | ~ r1_tarski(X0,k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_6514,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,X0))
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
    | ~ r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(k8_relat_1(sK5,X0)) ),
    inference(instantiation,[status(thm)],[c_5305])).

cnf(c_6515,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,X0)) != iProver_top
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7)) = iProver_top
    | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7)) != iProver_top
    | v1_relat_1(k8_relat_1(sK5,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6514])).

cnf(c_6517,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7)) = iProver_top
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK6)) != iProver_top
    | r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7)) != iProver_top
    | v1_relat_1(k8_relat_1(sK5,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6515])).

cnf(c_2905,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(sK5,X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2906,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(sK5,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2905])).

cnf(c_2908,plain,
    ( v1_relat_1(k8_relat_1(sK5,sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2906])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1361,plain,
    ( ~ r1_tarski(X0,sK7)
    | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1366,plain,
    ( r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_1368,plain,
    ( r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7)) = iProver_top
    | r1_tarski(sK6,sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_668,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),k8_relat_1(X0,X1))
    | r1_tarski(k8_relat_1(X0,X1),X2)
    | ~ v1_relat_1(k8_relat_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1056,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_1057,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6)) = iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) = iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_765,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_766,plain,
    ( v1_relat_1(k8_relat_1(sK4,sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_635,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
    | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_636,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7)) != iProver_top
    | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) = iProver_top
    | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,plain,
    ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,plain,
    ( r1_tarski(sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13043,c_10491,c_6517,c_2908,c_1368,c_1057,c_766,c_636,c_22,c_20,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.32/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.32/1.00  
% 3.32/1.00  ------  iProver source info
% 3.32/1.00  
% 3.32/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.32/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.32/1.00  git: non_committed_changes: false
% 3.32/1.00  git: last_make_outside_of_git: false
% 3.32/1.00  
% 3.32/1.00  ------ 
% 3.32/1.00  
% 3.32/1.00  ------ Input Options
% 3.32/1.00  
% 3.32/1.00  --out_options                           all
% 3.32/1.00  --tptp_safe_out                         true
% 3.32/1.00  --problem_path                          ""
% 3.32/1.00  --include_path                          ""
% 3.32/1.00  --clausifier                            res/vclausify_rel
% 3.32/1.00  --clausifier_options                    --mode clausify
% 3.32/1.00  --stdin                                 false
% 3.32/1.00  --stats_out                             sel
% 3.32/1.00  
% 3.32/1.00  ------ General Options
% 3.32/1.00  
% 3.32/1.00  --fof                                   false
% 3.32/1.00  --time_out_real                         604.99
% 3.32/1.00  --time_out_virtual                      -1.
% 3.32/1.00  --symbol_type_check                     false
% 3.32/1.00  --clausify_out                          false
% 3.32/1.00  --sig_cnt_out                           false
% 3.32/1.00  --trig_cnt_out                          false
% 3.32/1.00  --trig_cnt_out_tolerance                1.
% 3.32/1.00  --trig_cnt_out_sk_spl                   false
% 3.32/1.00  --abstr_cl_out                          false
% 3.32/1.00  
% 3.32/1.00  ------ Global Options
% 3.32/1.00  
% 3.32/1.00  --schedule                              none
% 3.32/1.00  --add_important_lit                     false
% 3.32/1.00  --prop_solver_per_cl                    1000
% 3.32/1.00  --min_unsat_core                        false
% 3.32/1.00  --soft_assumptions                      false
% 3.32/1.00  --soft_lemma_size                       3
% 3.32/1.00  --prop_impl_unit_size                   0
% 3.32/1.00  --prop_impl_unit                        []
% 3.32/1.00  --share_sel_clauses                     true
% 3.32/1.00  --reset_solvers                         false
% 3.32/1.00  --bc_imp_inh                            [conj_cone]
% 3.32/1.00  --conj_cone_tolerance                   3.
% 3.32/1.00  --extra_neg_conj                        none
% 3.32/1.00  --large_theory_mode                     true
% 3.32/1.00  --prolific_symb_bound                   200
% 3.32/1.00  --lt_threshold                          2000
% 3.32/1.00  --clause_weak_htbl                      true
% 3.32/1.00  --gc_record_bc_elim                     false
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing Options
% 3.32/1.00  
% 3.32/1.00  --preprocessing_flag                    true
% 3.32/1.00  --time_out_prep_mult                    0.1
% 3.32/1.00  --splitting_mode                        input
% 3.32/1.00  --splitting_grd                         true
% 3.32/1.00  --splitting_cvd                         false
% 3.32/1.00  --splitting_cvd_svl                     false
% 3.32/1.00  --splitting_nvd                         32
% 3.32/1.00  --sub_typing                            true
% 3.32/1.00  --prep_gs_sim                           false
% 3.32/1.00  --prep_unflatten                        true
% 3.32/1.00  --prep_res_sim                          true
% 3.32/1.00  --prep_upred                            true
% 3.32/1.00  --prep_sem_filter                       exhaustive
% 3.32/1.00  --prep_sem_filter_out                   false
% 3.32/1.00  --pred_elim                             false
% 3.32/1.00  --res_sim_input                         true
% 3.32/1.00  --eq_ax_congr_red                       true
% 3.32/1.00  --pure_diseq_elim                       true
% 3.32/1.00  --brand_transform                       false
% 3.32/1.00  --non_eq_to_eq                          false
% 3.32/1.00  --prep_def_merge                        true
% 3.32/1.00  --prep_def_merge_prop_impl              false
% 3.32/1.00  --prep_def_merge_mbd                    true
% 3.32/1.00  --prep_def_merge_tr_red                 false
% 3.32/1.00  --prep_def_merge_tr_cl                  false
% 3.32/1.00  --smt_preprocessing                     true
% 3.32/1.00  --smt_ac_axioms                         fast
% 3.32/1.00  --preprocessed_out                      false
% 3.32/1.00  --preprocessed_stats                    false
% 3.32/1.00  
% 3.32/1.00  ------ Abstraction refinement Options
% 3.32/1.00  
% 3.32/1.00  --abstr_ref                             []
% 3.32/1.00  --abstr_ref_prep                        false
% 3.32/1.00  --abstr_ref_until_sat                   false
% 3.32/1.00  --abstr_ref_sig_restrict                funpre
% 3.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/1.00  --abstr_ref_under                       []
% 3.32/1.00  
% 3.32/1.00  ------ SAT Options
% 3.32/1.00  
% 3.32/1.00  --sat_mode                              false
% 3.32/1.00  --sat_fm_restart_options                ""
% 3.32/1.00  --sat_gr_def                            false
% 3.32/1.00  --sat_epr_types                         true
% 3.32/1.00  --sat_non_cyclic_types                  false
% 3.32/1.00  --sat_finite_models                     false
% 3.32/1.00  --sat_fm_lemmas                         false
% 3.32/1.00  --sat_fm_prep                           false
% 3.32/1.00  --sat_fm_uc_incr                        true
% 3.32/1.00  --sat_out_model                         small
% 3.32/1.00  --sat_out_clauses                       false
% 3.32/1.00  
% 3.32/1.00  ------ QBF Options
% 3.32/1.00  
% 3.32/1.00  --qbf_mode                              false
% 3.32/1.00  --qbf_elim_univ                         false
% 3.32/1.00  --qbf_dom_inst                          none
% 3.32/1.00  --qbf_dom_pre_inst                      false
% 3.32/1.00  --qbf_sk_in                             false
% 3.32/1.00  --qbf_pred_elim                         true
% 3.32/1.00  --qbf_split                             512
% 3.32/1.00  
% 3.32/1.00  ------ BMC1 Options
% 3.32/1.00  
% 3.32/1.00  --bmc1_incremental                      false
% 3.32/1.00  --bmc1_axioms                           reachable_all
% 3.32/1.00  --bmc1_min_bound                        0
% 3.32/1.00  --bmc1_max_bound                        -1
% 3.32/1.00  --bmc1_max_bound_default                -1
% 3.32/1.00  --bmc1_symbol_reachability              true
% 3.32/1.00  --bmc1_property_lemmas                  false
% 3.32/1.00  --bmc1_k_induction                      false
% 3.32/1.00  --bmc1_non_equiv_states                 false
% 3.32/1.00  --bmc1_deadlock                         false
% 3.32/1.00  --bmc1_ucm                              false
% 3.32/1.00  --bmc1_add_unsat_core                   none
% 3.32/1.00  --bmc1_unsat_core_children              false
% 3.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/1.00  --bmc1_out_stat                         full
% 3.32/1.00  --bmc1_ground_init                      false
% 3.32/1.00  --bmc1_pre_inst_next_state              false
% 3.32/1.00  --bmc1_pre_inst_state                   false
% 3.32/1.00  --bmc1_pre_inst_reach_state             false
% 3.32/1.00  --bmc1_out_unsat_core                   false
% 3.32/1.00  --bmc1_aig_witness_out                  false
% 3.32/1.00  --bmc1_verbose                          false
% 3.32/1.00  --bmc1_dump_clauses_tptp                false
% 3.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.32/1.00  --bmc1_dump_file                        -
% 3.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.32/1.00  --bmc1_ucm_extend_mode                  1
% 3.32/1.00  --bmc1_ucm_init_mode                    2
% 3.32/1.00  --bmc1_ucm_cone_mode                    none
% 3.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.32/1.00  --bmc1_ucm_relax_model                  4
% 3.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/1.00  --bmc1_ucm_layered_model                none
% 3.32/1.00  --bmc1_ucm_max_lemma_size               10
% 3.32/1.00  
% 3.32/1.00  ------ AIG Options
% 3.32/1.00  
% 3.32/1.00  --aig_mode                              false
% 3.32/1.00  
% 3.32/1.00  ------ Instantiation Options
% 3.32/1.00  
% 3.32/1.00  --instantiation_flag                    true
% 3.32/1.00  --inst_sos_flag                         false
% 3.32/1.00  --inst_sos_phase                        true
% 3.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/1.00  --inst_lit_sel_side                     num_symb
% 3.32/1.00  --inst_solver_per_active                1400
% 3.32/1.00  --inst_solver_calls_frac                1.
% 3.32/1.00  --inst_passive_queue_type               priority_queues
% 3.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/1.00  --inst_passive_queues_freq              [25;2]
% 3.32/1.00  --inst_dismatching                      true
% 3.32/1.00  --inst_eager_unprocessed_to_passive     true
% 3.32/1.00  --inst_prop_sim_given                   true
% 3.32/1.00  --inst_prop_sim_new                     false
% 3.32/1.00  --inst_subs_new                         false
% 3.32/1.00  --inst_eq_res_simp                      false
% 3.32/1.00  --inst_subs_given                       false
% 3.32/1.00  --inst_orphan_elimination               true
% 3.32/1.00  --inst_learning_loop_flag               true
% 3.32/1.00  --inst_learning_start                   3000
% 3.32/1.00  --inst_learning_factor                  2
% 3.32/1.00  --inst_start_prop_sim_after_learn       3
% 3.32/1.00  --inst_sel_renew                        solver
% 3.32/1.00  --inst_lit_activity_flag                true
% 3.32/1.00  --inst_restr_to_given                   false
% 3.32/1.00  --inst_activity_threshold               500
% 3.32/1.00  --inst_out_proof                        true
% 3.32/1.00  
% 3.32/1.00  ------ Resolution Options
% 3.32/1.00  
% 3.32/1.00  --resolution_flag                       true
% 3.32/1.00  --res_lit_sel                           adaptive
% 3.32/1.00  --res_lit_sel_side                      none
% 3.32/1.00  --res_ordering                          kbo
% 3.32/1.00  --res_to_prop_solver                    active
% 3.32/1.00  --res_prop_simpl_new                    false
% 3.32/1.00  --res_prop_simpl_given                  true
% 3.32/1.00  --res_passive_queue_type                priority_queues
% 3.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/1.00  --res_passive_queues_freq               [15;5]
% 3.32/1.00  --res_forward_subs                      full
% 3.32/1.00  --res_backward_subs                     full
% 3.32/1.00  --res_forward_subs_resolution           true
% 3.32/1.00  --res_backward_subs_resolution          true
% 3.32/1.00  --res_orphan_elimination                true
% 3.32/1.00  --res_time_limit                        2.
% 3.32/1.00  --res_out_proof                         true
% 3.32/1.00  
% 3.32/1.00  ------ Superposition Options
% 3.32/1.00  
% 3.32/1.00  --superposition_flag                    true
% 3.32/1.00  --sup_passive_queue_type                priority_queues
% 3.32/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/1.00  --sup_passive_queues_freq               [1;4]
% 3.32/1.00  --demod_completeness_check              fast
% 3.32/1.00  --demod_use_ground                      true
% 3.32/1.00  --sup_to_prop_solver                    passive
% 3.32/1.00  --sup_prop_simpl_new                    true
% 3.32/1.00  --sup_prop_simpl_given                  true
% 3.32/1.00  --sup_fun_splitting                     false
% 3.32/1.00  --sup_smt_interval                      50000
% 3.32/1.00  
% 3.32/1.00  ------ Superposition Simplification Setup
% 3.32/1.00  
% 3.32/1.00  --sup_indices_passive                   []
% 3.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_full_bw                           [BwDemod]
% 3.32/1.00  --sup_immed_triv                        [TrivRules]
% 3.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_immed_bw_main                     []
% 3.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.00  
% 3.32/1.00  ------ Combination Options
% 3.32/1.00  
% 3.32/1.00  --comb_res_mult                         3
% 3.32/1.00  --comb_sup_mult                         2
% 3.32/1.00  --comb_inst_mult                        10
% 3.32/1.00  
% 3.32/1.00  ------ Debug Options
% 3.32/1.00  
% 3.32/1.00  --dbg_backtrace                         false
% 3.32/1.00  --dbg_dump_prop_clauses                 false
% 3.32/1.00  --dbg_dump_prop_clauses_file            -
% 3.32/1.00  --dbg_out_stat                          false
% 3.32/1.00  ------ Parsing...
% 3.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.32/1.00  ------ Proving...
% 3.32/1.00  ------ Problem Properties 
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  clauses                                 18
% 3.32/1.00  conjectures                             5
% 3.32/1.00  EPR                                     4
% 3.32/1.00  Horn                                    15
% 3.32/1.00  unary                                   5
% 3.32/1.00  binary                                  3
% 3.32/1.00  lits                                    54
% 3.32/1.00  lits eq                                 5
% 3.32/1.00  fd_pure                                 0
% 3.32/1.00  fd_pseudo                               0
% 3.32/1.00  fd_cond                                 0
% 3.32/1.00  fd_pseudo_cond                          3
% 3.32/1.00  AC symbols                              0
% 3.32/1.00  
% 3.32/1.00  ------ Input Options Time Limit: Unbounded
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  ------ 
% 3.32/1.00  Current options:
% 3.32/1.00  ------ 
% 3.32/1.00  
% 3.32/1.00  ------ Input Options
% 3.32/1.00  
% 3.32/1.00  --out_options                           all
% 3.32/1.00  --tptp_safe_out                         true
% 3.32/1.00  --problem_path                          ""
% 3.32/1.00  --include_path                          ""
% 3.32/1.00  --clausifier                            res/vclausify_rel
% 3.32/1.00  --clausifier_options                    --mode clausify
% 3.32/1.00  --stdin                                 false
% 3.32/1.00  --stats_out                             sel
% 3.32/1.00  
% 3.32/1.00  ------ General Options
% 3.32/1.00  
% 3.32/1.00  --fof                                   false
% 3.32/1.00  --time_out_real                         604.99
% 3.32/1.00  --time_out_virtual                      -1.
% 3.32/1.00  --symbol_type_check                     false
% 3.32/1.00  --clausify_out                          false
% 3.32/1.00  --sig_cnt_out                           false
% 3.32/1.00  --trig_cnt_out                          false
% 3.32/1.00  --trig_cnt_out_tolerance                1.
% 3.32/1.00  --trig_cnt_out_sk_spl                   false
% 3.32/1.00  --abstr_cl_out                          false
% 3.32/1.00  
% 3.32/1.00  ------ Global Options
% 3.32/1.00  
% 3.32/1.00  --schedule                              none
% 3.32/1.00  --add_important_lit                     false
% 3.32/1.00  --prop_solver_per_cl                    1000
% 3.32/1.00  --min_unsat_core                        false
% 3.32/1.00  --soft_assumptions                      false
% 3.32/1.00  --soft_lemma_size                       3
% 3.32/1.00  --prop_impl_unit_size                   0
% 3.32/1.00  --prop_impl_unit                        []
% 3.32/1.00  --share_sel_clauses                     true
% 3.32/1.00  --reset_solvers                         false
% 3.32/1.00  --bc_imp_inh                            [conj_cone]
% 3.32/1.00  --conj_cone_tolerance                   3.
% 3.32/1.00  --extra_neg_conj                        none
% 3.32/1.00  --large_theory_mode                     true
% 3.32/1.00  --prolific_symb_bound                   200
% 3.32/1.00  --lt_threshold                          2000
% 3.32/1.00  --clause_weak_htbl                      true
% 3.32/1.00  --gc_record_bc_elim                     false
% 3.32/1.00  
% 3.32/1.00  ------ Preprocessing Options
% 3.32/1.00  
% 3.32/1.00  --preprocessing_flag                    true
% 3.32/1.00  --time_out_prep_mult                    0.1
% 3.32/1.00  --splitting_mode                        input
% 3.32/1.00  --splitting_grd                         true
% 3.32/1.00  --splitting_cvd                         false
% 3.32/1.00  --splitting_cvd_svl                     false
% 3.32/1.00  --splitting_nvd                         32
% 3.32/1.00  --sub_typing                            true
% 3.32/1.00  --prep_gs_sim                           false
% 3.32/1.00  --prep_unflatten                        true
% 3.32/1.00  --prep_res_sim                          true
% 3.32/1.00  --prep_upred                            true
% 3.32/1.00  --prep_sem_filter                       exhaustive
% 3.32/1.00  --prep_sem_filter_out                   false
% 3.32/1.00  --pred_elim                             false
% 3.32/1.00  --res_sim_input                         true
% 3.32/1.00  --eq_ax_congr_red                       true
% 3.32/1.00  --pure_diseq_elim                       true
% 3.32/1.00  --brand_transform                       false
% 3.32/1.00  --non_eq_to_eq                          false
% 3.32/1.00  --prep_def_merge                        true
% 3.32/1.00  --prep_def_merge_prop_impl              false
% 3.32/1.00  --prep_def_merge_mbd                    true
% 3.32/1.00  --prep_def_merge_tr_red                 false
% 3.32/1.00  --prep_def_merge_tr_cl                  false
% 3.32/1.00  --smt_preprocessing                     true
% 3.32/1.00  --smt_ac_axioms                         fast
% 3.32/1.00  --preprocessed_out                      false
% 3.32/1.00  --preprocessed_stats                    false
% 3.32/1.00  
% 3.32/1.00  ------ Abstraction refinement Options
% 3.32/1.00  
% 3.32/1.00  --abstr_ref                             []
% 3.32/1.00  --abstr_ref_prep                        false
% 3.32/1.00  --abstr_ref_until_sat                   false
% 3.32/1.00  --abstr_ref_sig_restrict                funpre
% 3.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.32/1.00  --abstr_ref_under                       []
% 3.32/1.00  
% 3.32/1.00  ------ SAT Options
% 3.32/1.00  
% 3.32/1.00  --sat_mode                              false
% 3.32/1.00  --sat_fm_restart_options                ""
% 3.32/1.00  --sat_gr_def                            false
% 3.32/1.00  --sat_epr_types                         true
% 3.32/1.00  --sat_non_cyclic_types                  false
% 3.32/1.00  --sat_finite_models                     false
% 3.32/1.00  --sat_fm_lemmas                         false
% 3.32/1.00  --sat_fm_prep                           false
% 3.32/1.00  --sat_fm_uc_incr                        true
% 3.32/1.00  --sat_out_model                         small
% 3.32/1.00  --sat_out_clauses                       false
% 3.32/1.00  
% 3.32/1.00  ------ QBF Options
% 3.32/1.00  
% 3.32/1.00  --qbf_mode                              false
% 3.32/1.00  --qbf_elim_univ                         false
% 3.32/1.00  --qbf_dom_inst                          none
% 3.32/1.00  --qbf_dom_pre_inst                      false
% 3.32/1.00  --qbf_sk_in                             false
% 3.32/1.00  --qbf_pred_elim                         true
% 3.32/1.00  --qbf_split                             512
% 3.32/1.00  
% 3.32/1.00  ------ BMC1 Options
% 3.32/1.00  
% 3.32/1.00  --bmc1_incremental                      false
% 3.32/1.00  --bmc1_axioms                           reachable_all
% 3.32/1.00  --bmc1_min_bound                        0
% 3.32/1.00  --bmc1_max_bound                        -1
% 3.32/1.00  --bmc1_max_bound_default                -1
% 3.32/1.00  --bmc1_symbol_reachability              true
% 3.32/1.00  --bmc1_property_lemmas                  false
% 3.32/1.00  --bmc1_k_induction                      false
% 3.32/1.00  --bmc1_non_equiv_states                 false
% 3.32/1.00  --bmc1_deadlock                         false
% 3.32/1.00  --bmc1_ucm                              false
% 3.32/1.00  --bmc1_add_unsat_core                   none
% 3.32/1.00  --bmc1_unsat_core_children              false
% 3.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.32/1.00  --bmc1_out_stat                         full
% 3.32/1.00  --bmc1_ground_init                      false
% 3.32/1.00  --bmc1_pre_inst_next_state              false
% 3.32/1.00  --bmc1_pre_inst_state                   false
% 3.32/1.00  --bmc1_pre_inst_reach_state             false
% 3.32/1.00  --bmc1_out_unsat_core                   false
% 3.32/1.00  --bmc1_aig_witness_out                  false
% 3.32/1.00  --bmc1_verbose                          false
% 3.32/1.00  --bmc1_dump_clauses_tptp                false
% 3.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.32/1.00  --bmc1_dump_file                        -
% 3.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.32/1.00  --bmc1_ucm_extend_mode                  1
% 3.32/1.00  --bmc1_ucm_init_mode                    2
% 3.32/1.00  --bmc1_ucm_cone_mode                    none
% 3.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.32/1.00  --bmc1_ucm_relax_model                  4
% 3.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.32/1.00  --bmc1_ucm_layered_model                none
% 3.32/1.00  --bmc1_ucm_max_lemma_size               10
% 3.32/1.00  
% 3.32/1.00  ------ AIG Options
% 3.32/1.00  
% 3.32/1.00  --aig_mode                              false
% 3.32/1.00  
% 3.32/1.00  ------ Instantiation Options
% 3.32/1.00  
% 3.32/1.00  --instantiation_flag                    true
% 3.32/1.00  --inst_sos_flag                         false
% 3.32/1.00  --inst_sos_phase                        true
% 3.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.32/1.00  --inst_lit_sel_side                     num_symb
% 3.32/1.00  --inst_solver_per_active                1400
% 3.32/1.00  --inst_solver_calls_frac                1.
% 3.32/1.00  --inst_passive_queue_type               priority_queues
% 3.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.32/1.00  --inst_passive_queues_freq              [25;2]
% 3.32/1.00  --inst_dismatching                      true
% 3.32/1.00  --inst_eager_unprocessed_to_passive     true
% 3.32/1.00  --inst_prop_sim_given                   true
% 3.32/1.00  --inst_prop_sim_new                     false
% 3.32/1.00  --inst_subs_new                         false
% 3.32/1.00  --inst_eq_res_simp                      false
% 3.32/1.00  --inst_subs_given                       false
% 3.32/1.00  --inst_orphan_elimination               true
% 3.32/1.00  --inst_learning_loop_flag               true
% 3.32/1.00  --inst_learning_start                   3000
% 3.32/1.00  --inst_learning_factor                  2
% 3.32/1.00  --inst_start_prop_sim_after_learn       3
% 3.32/1.00  --inst_sel_renew                        solver
% 3.32/1.00  --inst_lit_activity_flag                true
% 3.32/1.00  --inst_restr_to_given                   false
% 3.32/1.00  --inst_activity_threshold               500
% 3.32/1.00  --inst_out_proof                        true
% 3.32/1.00  
% 3.32/1.00  ------ Resolution Options
% 3.32/1.00  
% 3.32/1.00  --resolution_flag                       true
% 3.32/1.00  --res_lit_sel                           adaptive
% 3.32/1.00  --res_lit_sel_side                      none
% 3.32/1.00  --res_ordering                          kbo
% 3.32/1.00  --res_to_prop_solver                    active
% 3.32/1.00  --res_prop_simpl_new                    false
% 3.32/1.00  --res_prop_simpl_given                  true
% 3.32/1.00  --res_passive_queue_type                priority_queues
% 3.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.32/1.00  --res_passive_queues_freq               [15;5]
% 3.32/1.00  --res_forward_subs                      full
% 3.32/1.00  --res_backward_subs                     full
% 3.32/1.00  --res_forward_subs_resolution           true
% 3.32/1.00  --res_backward_subs_resolution          true
% 3.32/1.00  --res_orphan_elimination                true
% 3.32/1.00  --res_time_limit                        2.
% 3.32/1.00  --res_out_proof                         true
% 3.32/1.00  
% 3.32/1.00  ------ Superposition Options
% 3.32/1.00  
% 3.32/1.00  --superposition_flag                    true
% 3.32/1.00  --sup_passive_queue_type                priority_queues
% 3.32/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.32/1.00  --sup_passive_queues_freq               [1;4]
% 3.32/1.00  --demod_completeness_check              fast
% 3.32/1.00  --demod_use_ground                      true
% 3.32/1.00  --sup_to_prop_solver                    passive
% 3.32/1.00  --sup_prop_simpl_new                    true
% 3.32/1.00  --sup_prop_simpl_given                  true
% 3.32/1.00  --sup_fun_splitting                     false
% 3.32/1.00  --sup_smt_interval                      50000
% 3.32/1.00  
% 3.32/1.00  ------ Superposition Simplification Setup
% 3.32/1.00  
% 3.32/1.00  --sup_indices_passive                   []
% 3.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_full_bw                           [BwDemod]
% 3.32/1.00  --sup_immed_triv                        [TrivRules]
% 3.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_immed_bw_main                     []
% 3.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.32/1.00  
% 3.32/1.00  ------ Combination Options
% 3.32/1.00  
% 3.32/1.00  --comb_res_mult                         3
% 3.32/1.00  --comb_sup_mult                         2
% 3.32/1.00  --comb_inst_mult                        10
% 3.32/1.00  
% 3.32/1.00  ------ Debug Options
% 3.32/1.00  
% 3.32/1.00  --dbg_backtrace                         false
% 3.32/1.00  --dbg_dump_prop_clauses                 false
% 3.32/1.00  --dbg_dump_prop_clauses_file            -
% 3.32/1.00  --dbg_out_stat                          false
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  ------ Proving...
% 3.32/1.00  
% 3.32/1.00  
% 3.32/1.00  % SZS status Theorem for theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.32/1.00  
% 3.32/1.00  fof(f7,conjecture,(
% 3.32/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 3.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f8,negated_conjecture,(
% 3.32/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 3.32/1.00    inference(negated_conjecture,[],[f7])).
% 3.32/1.00  
% 3.32/1.00  fof(f16,plain,(
% 3.32/1.00    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 3.32/1.00    inference(ennf_transformation,[],[f8])).
% 3.32/1.00  
% 3.32/1.00  fof(f17,plain,(
% 3.32/1.00    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 3.32/1.00    inference(flattening,[],[f16])).
% 3.32/1.00  
% 3.32/1.00  fof(f28,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,sK7)) & r1_tarski(X0,X1) & r1_tarski(X2,sK7) & v1_relat_1(sK7))) )),
% 3.32/1.00    introduced(choice_axiom,[])).
% 3.32/1.00  
% 3.32/1.00  fof(f27,plain,(
% 3.32/1.00    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X3)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,X3) & v1_relat_1(X3)) & v1_relat_1(sK6))),
% 3.32/1.00    introduced(choice_axiom,[])).
% 3.32/1.00  
% 3.32/1.00  fof(f29,plain,(
% 3.32/1.00    (~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) & r1_tarski(sK4,sK5) & r1_tarski(sK6,sK7) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 3.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f17,f28,f27])).
% 3.32/1.00  
% 3.32/1.00  fof(f46,plain,(
% 3.32/1.00    r1_tarski(sK4,sK5)),
% 3.32/1.00    inference(cnf_transformation,[],[f29])).
% 3.32/1.00  
% 3.32/1.00  fof(f1,axiom,(
% 3.32/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f9,plain,(
% 3.32/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.32/1.00    inference(ennf_transformation,[],[f1])).
% 3.32/1.00  
% 3.32/1.00  fof(f30,plain,(
% 3.32/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f9])).
% 3.32/1.00  
% 3.32/1.00  fof(f43,plain,(
% 3.32/1.00    v1_relat_1(sK6)),
% 3.32/1.00    inference(cnf_transformation,[],[f29])).
% 3.32/1.00  
% 3.32/1.00  fof(f5,axiom,(
% 3.32/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 3.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f13,plain,(
% 3.32/1.00    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.32/1.00    inference(ennf_transformation,[],[f5])).
% 3.32/1.00  
% 3.32/1.00  fof(f41,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f13])).
% 3.32/1.00  
% 3.32/1.00  fof(f3,axiom,(
% 3.32/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f11,plain,(
% 3.32/1.00    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.32/1.00    inference(ennf_transformation,[],[f3])).
% 3.32/1.00  
% 3.32/1.00  fof(f23,plain,(
% 3.32/1.00    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.32/1.00    inference(nnf_transformation,[],[f11])).
% 3.32/1.00  
% 3.32/1.00  fof(f24,plain,(
% 3.32/1.00    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.32/1.00    inference(rectify,[],[f23])).
% 3.32/1.00  
% 3.32/1.00  fof(f25,plain,(
% 3.32/1.00    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))),
% 3.32/1.00    introduced(choice_axiom,[])).
% 3.32/1.00  
% 3.32/1.00  fof(f26,plain,(
% 3.32/1.00    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).
% 3.32/1.00  
% 3.32/1.00  fof(f38,plain,(
% 3.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f26])).
% 3.32/1.00  
% 3.32/1.00  fof(f2,axiom,(
% 3.32/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 3.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f10,plain,(
% 3.32/1.00    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.32/1.00    inference(ennf_transformation,[],[f2])).
% 3.32/1.00  
% 3.32/1.00  fof(f18,plain,(
% 3.32/1.00    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.32/1.00    inference(nnf_transformation,[],[f10])).
% 3.32/1.00  
% 3.32/1.00  fof(f19,plain,(
% 3.32/1.00    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.32/1.00    inference(flattening,[],[f18])).
% 3.32/1.00  
% 3.32/1.00  fof(f20,plain,(
% 3.32/1.00    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.32/1.00    inference(rectify,[],[f19])).
% 3.32/1.00  
% 3.32/1.00  fof(f21,plain,(
% 3.32/1.00    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 3.32/1.00    introduced(choice_axiom,[])).
% 3.32/1.00  
% 3.32/1.00  fof(f22,plain,(
% 3.32/1.00    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 3.32/1.00  
% 3.32/1.00  fof(f32,plain,(
% 3.32/1.00    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f22])).
% 3.32/1.00  
% 3.32/1.00  fof(f49,plain,(
% 3.32/1.00    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.32/1.00    inference(equality_resolution,[],[f32])).
% 3.32/1.00  
% 3.32/1.00  fof(f4,axiom,(
% 3.32/1.00    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 3.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f12,plain,(
% 3.32/1.00    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 3.32/1.00    inference(ennf_transformation,[],[f4])).
% 3.32/1.00  
% 3.32/1.00  fof(f40,plain,(
% 3.32/1.00    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f12])).
% 3.32/1.00  
% 3.32/1.00  fof(f39,plain,(
% 3.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f26])).
% 3.32/1.00  
% 3.32/1.00  fof(f37,plain,(
% 3.32/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f26])).
% 3.32/1.00  
% 3.32/1.00  fof(f6,axiom,(
% 3.32/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 3.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.32/1.00  
% 3.32/1.00  fof(f14,plain,(
% 3.32/1.00    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.32/1.00    inference(ennf_transformation,[],[f6])).
% 3.32/1.00  
% 3.32/1.00  fof(f15,plain,(
% 3.32/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.32/1.00    inference(flattening,[],[f14])).
% 3.32/1.00  
% 3.32/1.00  fof(f42,plain,(
% 3.32/1.00    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.32/1.00    inference(cnf_transformation,[],[f15])).
% 3.32/1.00  
% 3.32/1.00  fof(f47,plain,(
% 3.32/1.00    ~r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),
% 3.32/1.00    inference(cnf_transformation,[],[f29])).
% 3.32/1.00  
% 3.32/1.00  fof(f45,plain,(
% 3.32/1.00    r1_tarski(sK6,sK7)),
% 3.32/1.00    inference(cnf_transformation,[],[f29])).
% 3.32/1.00  
% 3.32/1.00  fof(f44,plain,(
% 3.32/1.00    v1_relat_1(sK7)),
% 3.32/1.00    inference(cnf_transformation,[],[f29])).
% 3.32/1.00  
% 3.32/1.00  cnf(c_14,negated_conjecture,
% 3.32/1.00      ( r1_tarski(sK4,sK5) ),
% 3.32/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_455,plain,
% 3.32/1.00      ( r1_tarski(sK4,sK5) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_0,plain,
% 3.32/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.32/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_469,plain,
% 3.32/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_958,plain,
% 3.32/1.00      ( k3_xboole_0(sK4,sK5) = sK4 ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_455,c_469]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_17,negated_conjecture,
% 3.32/1.00      ( v1_relat_1(sK6) ),
% 3.32/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_452,plain,
% 3.32/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_11,plain,
% 3.32/1.00      ( ~ v1_relat_1(X0)
% 3.32/1.00      | k8_relat_1(k3_xboole_0(X1,X2),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_458,plain,
% 3.32/1.00      ( k8_relat_1(k3_xboole_0(X0,X1),X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
% 3.32/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1096,plain,
% 3.32/1.00      ( k8_relat_1(X0,k8_relat_1(X1,sK6)) = k8_relat_1(k3_xboole_0(X0,X1),sK6) ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_452,c_458]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_1851,plain,
% 3.32/1.00      ( k8_relat_1(sK4,k8_relat_1(sK5,sK6)) = k8_relat_1(sK4,sK6) ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_958,c_1096]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8,plain,
% 3.32/1.00      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 3.32/1.00      | r1_tarski(X0,X1)
% 3.32/1.00      | ~ v1_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_461,plain,
% 3.32/1.00      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) = iProver_top
% 3.32/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.32/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_5,plain,
% 3.32/1.00      ( r2_hidden(k4_tarski(X0,X1),X2)
% 3.32/1.00      | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
% 3.32/1.00      | ~ v1_relat_1(X2)
% 3.32/1.00      | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_464,plain,
% 3.32/1.00      ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
% 3.32/1.00      | r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2)) != iProver_top
% 3.32/1.00      | v1_relat_1(X2) != iProver_top
% 3.32/1.00      | v1_relat_1(k8_relat_1(X3,X2)) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_10,plain,
% 3.32/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 3.32/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_459,plain,
% 3.32/1.00      ( v1_relat_1(X0) != iProver_top
% 3.32/1.00      | v1_relat_1(k8_relat_1(X1,X0)) = iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_532,plain,
% 3.32/1.00      ( r2_hidden(k4_tarski(X0,X1),X2) = iProver_top
% 3.32/1.00      | r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2)) != iProver_top
% 3.32/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.32/1.00      inference(forward_subsumption_resolution,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_464,c_459]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_2031,plain,
% 3.32/1.00      ( r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),X1) = iProver_top
% 3.32/1.00      | r1_tarski(k8_relat_1(X0,X1),X2) = iProver_top
% 3.32/1.00      | v1_relat_1(X1) != iProver_top
% 3.32/1.00      | v1_relat_1(k8_relat_1(X0,X1)) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_461,c_532]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8831,plain,
% 3.32/1.00      ( r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),X1) = iProver_top
% 3.32/1.00      | r1_tarski(k8_relat_1(X0,X1),X2) = iProver_top
% 3.32/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.32/1.00      inference(forward_subsumption_resolution,
% 3.32/1.00                [status(thm)],
% 3.32/1.00                [c_2031,c_459]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_7,plain,
% 3.32/1.00      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
% 3.32/1.00      | r1_tarski(X0,X1)
% 3.32/1.00      | ~ v1_relat_1(X0) ),
% 3.32/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_462,plain,
% 3.32/1.00      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) != iProver_top
% 3.32/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.32/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.32/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.32/1.00  
% 3.32/1.00  cnf(c_8854,plain,
% 3.32/1.00      ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
% 3.32/1.00      | v1_relat_1(X1) != iProver_top
% 3.32/1.00      | v1_relat_1(k8_relat_1(X0,X1)) != iProver_top ),
% 3.32/1.00      inference(superposition,[status(thm)],[c_8831,c_462]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_8981,plain,
% 3.32/1.01      ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
% 3.32/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.32/1.01      inference(forward_subsumption_resolution,
% 3.32/1.01                [status(thm)],
% 3.32/1.01                [c_8854,c_459]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_13043,plain,
% 3.32/1.01      ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) = iProver_top
% 3.32/1.01      | v1_relat_1(k8_relat_1(sK5,sK6)) != iProver_top ),
% 3.32/1.01      inference(superposition,[status(thm)],[c_1851,c_8981]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_9,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.32/1.01      | r2_hidden(k4_tarski(X0,X1),X3)
% 3.32/1.01      | ~ r1_tarski(X2,X3)
% 3.32/1.01      | ~ v1_relat_1(X2) ),
% 3.32/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_677,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X2)
% 3.32/1.01      | ~ r1_tarski(X0,X2)
% 3.32/1.01      | ~ v1_relat_1(X0) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_774,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),k8_relat_1(X2,X3))
% 3.32/1.01      | ~ r1_tarski(X0,k8_relat_1(X2,X3))
% 3.32/1.01      | ~ v1_relat_1(X0) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_677]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_1146,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),k8_relat_1(X0,X1))
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),k8_relat_1(X3,X4))
% 3.32/1.01      | ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X3,X4))
% 3.32/1.01      | ~ v1_relat_1(k8_relat_1(X0,X1)) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_774]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_2239,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(X0,X1))
% 3.32/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
% 3.32/1.01      | ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(X0,X1))
% 3.32/1.01      | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_1146]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_10488,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,X0))
% 3.32/1.01      | ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
% 3.32/1.01      | ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0))
% 3.32/1.01      | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_2239]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_10489,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,X0)) = iProver_top
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6)) != iProver_top
% 3.32/1.01      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,X0)) != iProver_top
% 3.32/1.01      | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_10488]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_10491,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK6)) = iProver_top
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6)) != iProver_top
% 3.32/1.01      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK6)) != iProver_top
% 3.32/1.01      | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_10489]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_785,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X2)
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X3)
% 3.32/1.01      | ~ r1_tarski(X2,X3)
% 3.32/1.01      | ~ v1_relat_1(X2) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_2252,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),X3)
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),X4)
% 3.32/1.01      | ~ r1_tarski(X3,X4)
% 3.32/1.01      | ~ v1_relat_1(X3) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_785]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_5305,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),X0)
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
% 3.32/1.01      | ~ r1_tarski(X0,k8_relat_1(sK5,sK7))
% 3.32/1.01      | ~ v1_relat_1(X0) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_2252]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_6514,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,X0))
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
% 3.32/1.01      | ~ r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7))
% 3.32/1.01      | ~ v1_relat_1(k8_relat_1(sK5,X0)) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_5305]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_6515,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,X0)) != iProver_top
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7)) = iProver_top
% 3.32/1.01      | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7)) != iProver_top
% 3.32/1.01      | v1_relat_1(k8_relat_1(sK5,X0)) != iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_6514]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_6517,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7)) = iProver_top
% 3.32/1.01      | r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK6)) != iProver_top
% 3.32/1.01      | r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7)) != iProver_top
% 3.32/1.01      | v1_relat_1(k8_relat_1(sK5,sK6)) != iProver_top ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_6515]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_2905,plain,
% 3.32/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(sK5,X0)) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_2906,plain,
% 3.32/1.01      ( v1_relat_1(X0) != iProver_top
% 3.32/1.01      | v1_relat_1(k8_relat_1(sK5,X0)) = iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_2905]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_2908,plain,
% 3.32/1.01      ( v1_relat_1(k8_relat_1(sK5,sK6)) = iProver_top
% 3.32/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_2906]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_12,plain,
% 3.32/1.01      ( ~ r1_tarski(X0,X1)
% 3.32/1.01      | r1_tarski(k8_relat_1(X2,X0),k8_relat_1(X2,X1))
% 3.32/1.01      | ~ v1_relat_1(X1)
% 3.32/1.01      | ~ v1_relat_1(X0) ),
% 3.32/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_1361,plain,
% 3.32/1.01      ( ~ r1_tarski(X0,sK7)
% 3.32/1.01      | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7))
% 3.32/1.01      | ~ v1_relat_1(X0)
% 3.32/1.01      | ~ v1_relat_1(sK7) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_1366,plain,
% 3.32/1.01      ( r1_tarski(X0,sK7) != iProver_top
% 3.32/1.01      | r1_tarski(k8_relat_1(sK5,X0),k8_relat_1(sK5,sK7)) = iProver_top
% 3.32/1.01      | v1_relat_1(X0) != iProver_top
% 3.32/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_1368,plain,
% 3.32/1.01      ( r1_tarski(k8_relat_1(sK5,sK6),k8_relat_1(sK5,sK7)) = iProver_top
% 3.32/1.01      | r1_tarski(sK6,sK7) != iProver_top
% 3.32/1.01      | v1_relat_1(sK7) != iProver_top
% 3.32/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_1366]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_668,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(X0,X1),X2),sK3(k8_relat_1(X0,X1),X2)),k8_relat_1(X0,X1))
% 3.32/1.01      | r1_tarski(k8_relat_1(X0,X1),X2)
% 3.32/1.01      | ~ v1_relat_1(k8_relat_1(X0,X1)) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_1056,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6))
% 3.32/1.01      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
% 3.32/1.01      | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_668]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_1057,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK4,sK6)) = iProver_top
% 3.32/1.01      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) = iProver_top
% 3.32/1.01      | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_765,plain,
% 3.32/1.01      ( v1_relat_1(k8_relat_1(sK4,sK6)) | ~ v1_relat_1(sK6) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_766,plain,
% 3.32/1.01      ( v1_relat_1(k8_relat_1(sK4,sK6)) = iProver_top
% 3.32/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_635,plain,
% 3.32/1.01      ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7))
% 3.32/1.01      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))
% 3.32/1.01      | ~ v1_relat_1(k8_relat_1(sK4,sK6)) ),
% 3.32/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_636,plain,
% 3.32/1.01      ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)),sK3(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7))),k8_relat_1(sK5,sK7)) != iProver_top
% 3.32/1.01      | r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) = iProver_top
% 3.32/1.01      | v1_relat_1(k8_relat_1(sK4,sK6)) != iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_13,negated_conjecture,
% 3.32/1.01      ( ~ r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) ),
% 3.32/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_22,plain,
% 3.32/1.01      ( r1_tarski(k8_relat_1(sK4,sK6),k8_relat_1(sK5,sK7)) != iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_15,negated_conjecture,
% 3.32/1.01      ( r1_tarski(sK6,sK7) ),
% 3.32/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_20,plain,
% 3.32/1.01      ( r1_tarski(sK6,sK7) = iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_16,negated_conjecture,
% 3.32/1.01      ( v1_relat_1(sK7) ),
% 3.32/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_19,plain,
% 3.32/1.01      ( v1_relat_1(sK7) = iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(c_18,plain,
% 3.32/1.01      ( v1_relat_1(sK6) = iProver_top ),
% 3.32/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.32/1.01  
% 3.32/1.01  cnf(contradiction,plain,
% 3.32/1.01      ( $false ),
% 3.32/1.01      inference(minisat,
% 3.32/1.01                [status(thm)],
% 3.32/1.01                [c_13043,c_10491,c_6517,c_2908,c_1368,c_1057,c_766,c_636,
% 3.32/1.01                 c_22,c_20,c_19,c_18]) ).
% 3.32/1.01  
% 3.32/1.01  
% 3.32/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.32/1.01  
% 3.32/1.01  ------                               Statistics
% 3.32/1.01  
% 3.32/1.01  ------ Selected
% 3.32/1.01  
% 3.32/1.01  total_time:                             0.449
% 3.32/1.01  
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:49:22 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  130 (3468 expanded)
%              Number of clauses        :   84 (1197 expanded)
%              Number of leaves         :   16 ( 885 expanded)
%              Depth                    :   38
%              Number of atoms          :  464 (16603 expanded)
%              Number of equality atoms :  264 (7623 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK5(X0)) = X0
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK5(X0)) = X0
      & v1_funct_1(sK5(X0))
      & v1_relat_1(sK5(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f26])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f24])).

fof(f42,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f7,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK6
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK6
              | k1_relat_1(X1) != sK6
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k1_xboole_0 != sK6
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK6
            | k1_relat_1(X1) != sK6
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f28])).

fof(f48,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_relat_1(X2) != sK6
      | k1_relat_1(X1) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f49,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK5(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_15,plain,
    ( k1_relat_1(sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != sK6
    | k1_relat_1(X1) != sK6 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_584,plain,
    ( X0 = X1
    | k1_relat_1(X0) != sK6
    | k1_relat_1(X1) != sK6
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_944,plain,
    ( sK4(X0,X1) = X2
    | k1_relat_1(X2) != sK6
    | sK6 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_584])).

cnf(c_13,plain,
    ( v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_33,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_36,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1098,plain,
    ( v1_relat_1(X2) != iProver_top
    | sK4(X0,X1) = X2
    | k1_relat_1(X2) != sK6
    | sK6 != X0
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_33,c_36])).

cnf(c_1099,plain,
    ( sK4(X0,X1) = X2
    | k1_relat_1(X2) != sK6
    | sK6 != X0
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1098])).

cnf(c_1105,plain,
    ( sK4(X0,X1) = sK5(X2)
    | sK6 != X2
    | sK6 != X0
    | v1_funct_1(sK5(X2)) != iProver_top
    | v1_relat_1(sK5(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1099])).

cnf(c_701,plain,
    ( sK5(X0) = X1
    | k1_relat_1(X1) != sK6
    | sK6 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK5(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_584])).

cnf(c_17,plain,
    ( v1_relat_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,plain,
    ( v1_relat_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v1_funct_1(sK5(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( v1_funct_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_813,plain,
    ( v1_relat_1(X1) != iProver_top
    | sK5(X0) = X1
    | k1_relat_1(X1) != sK6
    | sK6 != X0
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_701,c_23,c_26])).

cnf(c_814,plain,
    ( sK5(X0) = X1
    | k1_relat_1(X1) != sK6
    | sK6 != X0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_813])).

cnf(c_943,plain,
    ( sK4(X0,X1) = sK5(X2)
    | sK6 != X0
    | sK6 != X2
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_814])).

cnf(c_945,plain,
    ( ~ v1_funct_1(sK4(X0,X1))
    | ~ v1_relat_1(sK4(X0,X1))
    | sK4(X0,X1) = sK5(X2)
    | sK6 != X0
    | sK6 != X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_943])).

cnf(c_1113,plain,
    ( sK4(X0,X1) = sK5(X2)
    | sK6 != X2
    | sK6 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1105,c_13,c_12,c_945])).

cnf(c_1114,plain,
    ( sK4(X0,X1) = sK5(X2)
    | sK6 != X0
    | sK6 != X2 ),
    inference(renaming,[status(thm)],[c_1113])).

cnf(c_1116,plain,
    ( sK4(sK6,X0) = sK5(X1)
    | sK6 != X1 ),
    inference(equality_resolution,[status(thm)],[c_1114])).

cnf(c_1160,plain,
    ( sK4(sK6,X0) = sK5(sK6) ),
    inference(equality_resolution,[status(thm)],[c_1116])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_595,plain,
    ( k9_relat_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_588,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_208,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_582,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_597,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_582,c_2])).

cnf(c_1967,plain,
    ( k9_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(X0,X1,k1_xboole_0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_597])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_590,plain,
    ( k1_funct_1(sK4(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2610,plain,
    ( k1_funct_1(sK4(X0,X1),sK2(X2,X0,k1_xboole_0)) = X1
    | k9_relat_1(X2,X0) = k1_xboole_0
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_590])).

cnf(c_4737,plain,
    ( k1_funct_1(sK4(X0,X1),sK2(sK4(X2,X3),X0,k1_xboole_0)) = X1
    | k9_relat_1(sK4(X2,X3),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_588,c_2610])).

cnf(c_4799,plain,
    ( k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0)) = X2
    | k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1160,c_4737])).

cnf(c_5007,plain,
    ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
    | k1_relat_1(k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0))) = X2 ),
    inference(superposition,[status(thm)],[c_4799,c_11])).

cnf(c_5676,plain,
    ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
    | k1_relat_1(k1_relat_1(k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0)))) = X2 ),
    inference(superposition,[status(thm)],[c_5007,c_11])).

cnf(c_5895,plain,
    ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
    | k1_relat_1(k1_relat_1(k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5676,c_2])).

cnf(c_6115,plain,
    ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
    | k1_relat_1(X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5007,c_5895])).

cnf(c_5783,plain,
    ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
    | k1_relat_1(X2) = X3 ),
    inference(superposition,[status(thm)],[c_5007,c_5676])).

cnf(c_11592,plain,
    ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0 ),
    inference(equality_factoring,[status(thm)],[c_5783])).

cnf(c_11635,plain,
    ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6115,c_11592])).

cnf(c_11648,plain,
    ( k9_relat_1(sK5(sK6),sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1160,c_11635])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_594,plain,
    ( k9_relat_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_593,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1922,plain,
    ( k9_relat_1(X0,X1) = X2
    | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),k9_relat_1(X0,X3)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_593])).

cnf(c_14696,plain,
    ( k9_relat_1(sK5(sK6),X0) = X1
    | r2_hidden(sK2(sK5(sK6),X0,X1),sK6) != iProver_top
    | r2_hidden(sK1(sK5(sK6),X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK5(sK6),X0,X1),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11648,c_1922])).

cnf(c_1238,plain,
    ( v1_relat_1(sK5(sK6)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1239,plain,
    ( v1_relat_1(sK5(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_16368,plain,
    ( r2_hidden(sK1(sK5(sK6),X0,X1),k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK5(sK6),X0,X1),X1) = iProver_top
    | r2_hidden(sK2(sK5(sK6),X0,X1),sK6) != iProver_top
    | k9_relat_1(sK5(sK6),X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14696,c_1239])).

cnf(c_16369,plain,
    ( k9_relat_1(sK5(sK6),X0) = X1
    | r2_hidden(sK2(sK5(sK6),X0,X1),sK6) != iProver_top
    | r2_hidden(sK1(sK5(sK6),X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK5(sK6),X0,X1),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_16368])).

cnf(c_16374,plain,
    ( k9_relat_1(sK5(sK6),sK6) = X0
    | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top
    | r2_hidden(sK1(sK5(sK6),sK6,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_16369])).

cnf(c_16394,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top
    | r2_hidden(sK1(sK5(sK6),sK6,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16374,c_11648])).

cnf(c_17127,plain,
    ( r2_hidden(sK1(sK5(sK6),sK6,X0),k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16394,c_1239])).

cnf(c_17128,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top
    | r2_hidden(sK1(sK5(sK6),sK6,X0),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_17127])).

cnf(c_17151,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17128,c_597])).

cnf(c_17392,plain,
    ( k1_funct_1(sK4(X0,X1),sK1(sK5(sK6),sK6,X0)) = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_17151,c_590])).

cnf(c_17691,plain,
    ( k1_funct_1(sK5(sK6),sK1(sK5(sK6),sK6,sK6)) = X0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1160,c_17392])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_326,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_343,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_327,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_616,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_617,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_17701,plain,
    ( k1_funct_1(sK5(sK6),sK1(sK5(sK6),sK6,sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17691,c_18,c_343,c_617])).

cnf(c_17770,plain,
    ( X0 = X1 ),
    inference(superposition,[status(thm)],[c_17701,c_17701])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK5(X1),X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_587,plain,
    ( k1_funct_1(sK5(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2611,plain,
    ( k1_funct_1(sK5(X0),sK2(X1,X0,k1_xboole_0)) = k1_xboole_0
    | k9_relat_1(X1,X0) = k1_xboole_0
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_587])).

cnf(c_3433,plain,
    ( k1_funct_1(sK5(X0),sK2(sK4(X1,X2),X0,k1_xboole_0)) = k1_xboole_0
    | k9_relat_1(sK4(X1,X2),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_588,c_2611])).

cnf(c_4988,plain,
    ( k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0)) != sK6
    | k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
    | sK5(X2) = X3
    | sK6 != X2
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4799,c_814])).

cnf(c_5401,plain,
    ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
    | sK5(X2) = X3
    | sK6 != X2
    | sK6 != k1_xboole_0
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3433,c_4988])).

cnf(c_5478,plain,
    ( sK6 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5401,c_18,c_343,c_617])).

cnf(c_18262,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_17770,c_5478])).

cnf(c_18265,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18262])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18265,c_343])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.78/1.56  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/1.56  
% 7.78/1.56  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.56  
% 7.78/1.56  ------  iProver source info
% 7.78/1.56  
% 7.78/1.56  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.56  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.56  git: non_committed_changes: false
% 7.78/1.56  git: last_make_outside_of_git: false
% 7.78/1.56  
% 7.78/1.56  ------ 
% 7.78/1.56  
% 7.78/1.56  ------ Input Options
% 7.78/1.56  
% 7.78/1.56  --out_options                           all
% 7.78/1.56  --tptp_safe_out                         true
% 7.78/1.56  --problem_path                          ""
% 7.78/1.56  --include_path                          ""
% 7.78/1.56  --clausifier                            res/vclausify_rel
% 7.78/1.56  --clausifier_options                    ""
% 7.78/1.56  --stdin                                 false
% 7.78/1.56  --stats_out                             all
% 7.78/1.56  
% 7.78/1.56  ------ General Options
% 7.78/1.56  
% 7.78/1.56  --fof                                   false
% 7.78/1.56  --time_out_real                         305.
% 7.78/1.56  --time_out_virtual                      -1.
% 7.78/1.56  --symbol_type_check                     false
% 7.78/1.56  --clausify_out                          false
% 7.78/1.56  --sig_cnt_out                           false
% 7.78/1.56  --trig_cnt_out                          false
% 7.78/1.56  --trig_cnt_out_tolerance                1.
% 7.78/1.56  --trig_cnt_out_sk_spl                   false
% 7.78/1.56  --abstr_cl_out                          false
% 7.78/1.56  
% 7.78/1.56  ------ Global Options
% 7.78/1.56  
% 7.78/1.56  --schedule                              default
% 7.78/1.56  --add_important_lit                     false
% 7.78/1.56  --prop_solver_per_cl                    1000
% 7.78/1.56  --min_unsat_core                        false
% 7.78/1.56  --soft_assumptions                      false
% 7.78/1.56  --soft_lemma_size                       3
% 7.78/1.56  --prop_impl_unit_size                   0
% 7.78/1.56  --prop_impl_unit                        []
% 7.78/1.56  --share_sel_clauses                     true
% 7.78/1.56  --reset_solvers                         false
% 7.78/1.56  --bc_imp_inh                            [conj_cone]
% 7.78/1.56  --conj_cone_tolerance                   3.
% 7.78/1.56  --extra_neg_conj                        none
% 7.78/1.56  --large_theory_mode                     true
% 7.78/1.56  --prolific_symb_bound                   200
% 7.78/1.56  --lt_threshold                          2000
% 7.78/1.56  --clause_weak_htbl                      true
% 7.78/1.56  --gc_record_bc_elim                     false
% 7.78/1.56  
% 7.78/1.56  ------ Preprocessing Options
% 7.78/1.56  
% 7.78/1.56  --preprocessing_flag                    true
% 7.78/1.56  --time_out_prep_mult                    0.1
% 7.78/1.56  --splitting_mode                        input
% 7.78/1.56  --splitting_grd                         true
% 7.78/1.56  --splitting_cvd                         false
% 7.78/1.56  --splitting_cvd_svl                     false
% 7.78/1.56  --splitting_nvd                         32
% 7.78/1.56  --sub_typing                            true
% 7.78/1.56  --prep_gs_sim                           true
% 7.78/1.56  --prep_unflatten                        true
% 7.78/1.56  --prep_res_sim                          true
% 7.78/1.56  --prep_upred                            true
% 7.78/1.56  --prep_sem_filter                       exhaustive
% 7.78/1.56  --prep_sem_filter_out                   false
% 7.78/1.56  --pred_elim                             true
% 7.78/1.56  --res_sim_input                         true
% 7.78/1.56  --eq_ax_congr_red                       true
% 7.78/1.56  --pure_diseq_elim                       true
% 7.78/1.56  --brand_transform                       false
% 7.78/1.56  --non_eq_to_eq                          false
% 7.78/1.56  --prep_def_merge                        true
% 7.78/1.56  --prep_def_merge_prop_impl              false
% 7.78/1.56  --prep_def_merge_mbd                    true
% 7.78/1.56  --prep_def_merge_tr_red                 false
% 7.78/1.56  --prep_def_merge_tr_cl                  false
% 7.78/1.56  --smt_preprocessing                     true
% 7.78/1.56  --smt_ac_axioms                         fast
% 7.78/1.56  --preprocessed_out                      false
% 7.78/1.56  --preprocessed_stats                    false
% 7.78/1.56  
% 7.78/1.56  ------ Abstraction refinement Options
% 7.78/1.56  
% 7.78/1.56  --abstr_ref                             []
% 7.78/1.56  --abstr_ref_prep                        false
% 7.78/1.56  --abstr_ref_until_sat                   false
% 7.78/1.56  --abstr_ref_sig_restrict                funpre
% 7.78/1.56  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.56  --abstr_ref_under                       []
% 7.78/1.56  
% 7.78/1.56  ------ SAT Options
% 7.78/1.56  
% 7.78/1.56  --sat_mode                              false
% 7.78/1.56  --sat_fm_restart_options                ""
% 7.78/1.56  --sat_gr_def                            false
% 7.78/1.56  --sat_epr_types                         true
% 7.78/1.56  --sat_non_cyclic_types                  false
% 7.78/1.56  --sat_finite_models                     false
% 7.78/1.56  --sat_fm_lemmas                         false
% 7.78/1.56  --sat_fm_prep                           false
% 7.78/1.56  --sat_fm_uc_incr                        true
% 7.78/1.56  --sat_out_model                         small
% 7.78/1.56  --sat_out_clauses                       false
% 7.78/1.56  
% 7.78/1.56  ------ QBF Options
% 7.78/1.56  
% 7.78/1.56  --qbf_mode                              false
% 7.78/1.56  --qbf_elim_univ                         false
% 7.78/1.56  --qbf_dom_inst                          none
% 7.78/1.56  --qbf_dom_pre_inst                      false
% 7.78/1.56  --qbf_sk_in                             false
% 7.78/1.56  --qbf_pred_elim                         true
% 7.78/1.56  --qbf_split                             512
% 7.78/1.56  
% 7.78/1.56  ------ BMC1 Options
% 7.78/1.56  
% 7.78/1.56  --bmc1_incremental                      false
% 7.78/1.56  --bmc1_axioms                           reachable_all
% 7.78/1.56  --bmc1_min_bound                        0
% 7.78/1.56  --bmc1_max_bound                        -1
% 7.78/1.56  --bmc1_max_bound_default                -1
% 7.78/1.56  --bmc1_symbol_reachability              true
% 7.78/1.56  --bmc1_property_lemmas                  false
% 7.78/1.56  --bmc1_k_induction                      false
% 7.78/1.56  --bmc1_non_equiv_states                 false
% 7.78/1.56  --bmc1_deadlock                         false
% 7.78/1.56  --bmc1_ucm                              false
% 7.78/1.56  --bmc1_add_unsat_core                   none
% 7.78/1.56  --bmc1_unsat_core_children              false
% 7.78/1.56  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.56  --bmc1_out_stat                         full
% 7.78/1.56  --bmc1_ground_init                      false
% 7.78/1.56  --bmc1_pre_inst_next_state              false
% 7.78/1.56  --bmc1_pre_inst_state                   false
% 7.78/1.56  --bmc1_pre_inst_reach_state             false
% 7.78/1.56  --bmc1_out_unsat_core                   false
% 7.78/1.56  --bmc1_aig_witness_out                  false
% 7.78/1.56  --bmc1_verbose                          false
% 7.78/1.56  --bmc1_dump_clauses_tptp                false
% 7.78/1.56  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.56  --bmc1_dump_file                        -
% 7.78/1.56  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.56  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.56  --bmc1_ucm_extend_mode                  1
% 7.78/1.56  --bmc1_ucm_init_mode                    2
% 7.78/1.56  --bmc1_ucm_cone_mode                    none
% 7.78/1.56  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.56  --bmc1_ucm_relax_model                  4
% 7.78/1.56  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.56  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.56  --bmc1_ucm_layered_model                none
% 7.78/1.56  --bmc1_ucm_max_lemma_size               10
% 7.78/1.56  
% 7.78/1.56  ------ AIG Options
% 7.78/1.56  
% 7.78/1.56  --aig_mode                              false
% 7.78/1.56  
% 7.78/1.56  ------ Instantiation Options
% 7.78/1.56  
% 7.78/1.56  --instantiation_flag                    true
% 7.78/1.56  --inst_sos_flag                         true
% 7.78/1.56  --inst_sos_phase                        true
% 7.78/1.56  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.56  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.56  --inst_lit_sel_side                     num_symb
% 7.78/1.56  --inst_solver_per_active                1400
% 7.78/1.56  --inst_solver_calls_frac                1.
% 7.78/1.56  --inst_passive_queue_type               priority_queues
% 7.78/1.56  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.56  --inst_passive_queues_freq              [25;2]
% 7.78/1.56  --inst_dismatching                      true
% 7.78/1.56  --inst_eager_unprocessed_to_passive     true
% 7.78/1.56  --inst_prop_sim_given                   true
% 7.78/1.56  --inst_prop_sim_new                     false
% 7.78/1.56  --inst_subs_new                         false
% 7.78/1.56  --inst_eq_res_simp                      false
% 7.78/1.56  --inst_subs_given                       false
% 7.78/1.56  --inst_orphan_elimination               true
% 7.78/1.56  --inst_learning_loop_flag               true
% 7.78/1.56  --inst_learning_start                   3000
% 7.78/1.56  --inst_learning_factor                  2
% 7.78/1.56  --inst_start_prop_sim_after_learn       3
% 7.78/1.56  --inst_sel_renew                        solver
% 7.78/1.56  --inst_lit_activity_flag                true
% 7.78/1.56  --inst_restr_to_given                   false
% 7.78/1.56  --inst_activity_threshold               500
% 7.78/1.56  --inst_out_proof                        true
% 7.78/1.56  
% 7.78/1.56  ------ Resolution Options
% 7.78/1.56  
% 7.78/1.56  --resolution_flag                       true
% 7.78/1.56  --res_lit_sel                           adaptive
% 7.78/1.56  --res_lit_sel_side                      none
% 7.78/1.56  --res_ordering                          kbo
% 7.78/1.56  --res_to_prop_solver                    active
% 7.78/1.56  --res_prop_simpl_new                    false
% 7.78/1.56  --res_prop_simpl_given                  true
% 7.78/1.56  --res_passive_queue_type                priority_queues
% 7.78/1.56  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.56  --res_passive_queues_freq               [15;5]
% 7.78/1.56  --res_forward_subs                      full
% 7.78/1.56  --res_backward_subs                     full
% 7.78/1.56  --res_forward_subs_resolution           true
% 7.78/1.56  --res_backward_subs_resolution          true
% 7.78/1.56  --res_orphan_elimination                true
% 7.78/1.56  --res_time_limit                        2.
% 7.78/1.56  --res_out_proof                         true
% 7.78/1.56  
% 7.78/1.56  ------ Superposition Options
% 7.78/1.56  
% 7.78/1.56  --superposition_flag                    true
% 7.78/1.56  --sup_passive_queue_type                priority_queues
% 7.78/1.56  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.56  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.56  --demod_completeness_check              fast
% 7.78/1.56  --demod_use_ground                      true
% 7.78/1.56  --sup_to_prop_solver                    passive
% 7.78/1.56  --sup_prop_simpl_new                    true
% 7.78/1.56  --sup_prop_simpl_given                  true
% 7.78/1.56  --sup_fun_splitting                     true
% 7.78/1.56  --sup_smt_interval                      50000
% 7.78/1.56  
% 7.78/1.56  ------ Superposition Simplification Setup
% 7.78/1.56  
% 7.78/1.56  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.56  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.56  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.56  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.56  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.56  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.56  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.56  --sup_immed_triv                        [TrivRules]
% 7.78/1.56  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.56  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.56  --sup_immed_bw_main                     []
% 7.78/1.56  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.56  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.56  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.56  --sup_input_bw                          []
% 7.78/1.56  
% 7.78/1.56  ------ Combination Options
% 7.78/1.56  
% 7.78/1.56  --comb_res_mult                         3
% 7.78/1.56  --comb_sup_mult                         2
% 7.78/1.56  --comb_inst_mult                        10
% 7.78/1.56  
% 7.78/1.56  ------ Debug Options
% 7.78/1.56  
% 7.78/1.56  --dbg_backtrace                         false
% 7.78/1.56  --dbg_dump_prop_clauses                 false
% 7.78/1.56  --dbg_dump_prop_clauses_file            -
% 7.78/1.56  --dbg_out_stat                          false
% 7.78/1.56  ------ Parsing...
% 7.78/1.56  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.56  
% 7.78/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.78/1.56  
% 7.78/1.56  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.56  
% 7.78/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.56  ------ Proving...
% 7.78/1.56  ------ Problem Properties 
% 7.78/1.56  
% 7.78/1.56  
% 7.78/1.56  clauses                                 19
% 7.78/1.56  conjectures                             2
% 7.78/1.56  EPR                                     1
% 7.78/1.56  Horn                                    17
% 7.78/1.56  unary                                   9
% 7.78/1.56  binary                                  3
% 7.78/1.56  lits                                    45
% 7.78/1.56  lits eq                                 12
% 7.78/1.56  fd_pure                                 0
% 7.78/1.56  fd_pseudo                               0
% 7.78/1.56  fd_cond                                 0
% 7.78/1.56  fd_pseudo_cond                          4
% 7.78/1.56  AC symbols                              0
% 7.78/1.56  
% 7.78/1.56  ------ Schedule dynamic 5 is on 
% 7.78/1.56  
% 7.78/1.56  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.78/1.56  
% 7.78/1.56  
% 7.78/1.56  ------ 
% 7.78/1.56  Current options:
% 7.78/1.56  ------ 
% 7.78/1.56  
% 7.78/1.56  ------ Input Options
% 7.78/1.56  
% 7.78/1.56  --out_options                           all
% 7.78/1.56  --tptp_safe_out                         true
% 7.78/1.56  --problem_path                          ""
% 7.78/1.56  --include_path                          ""
% 7.78/1.56  --clausifier                            res/vclausify_rel
% 7.78/1.56  --clausifier_options                    ""
% 7.78/1.56  --stdin                                 false
% 7.78/1.56  --stats_out                             all
% 7.78/1.56  
% 7.78/1.56  ------ General Options
% 7.78/1.56  
% 7.78/1.56  --fof                                   false
% 7.78/1.56  --time_out_real                         305.
% 7.78/1.56  --time_out_virtual                      -1.
% 7.78/1.56  --symbol_type_check                     false
% 7.78/1.56  --clausify_out                          false
% 7.78/1.56  --sig_cnt_out                           false
% 7.78/1.56  --trig_cnt_out                          false
% 7.78/1.56  --trig_cnt_out_tolerance                1.
% 7.78/1.56  --trig_cnt_out_sk_spl                   false
% 7.78/1.56  --abstr_cl_out                          false
% 7.78/1.56  
% 7.78/1.56  ------ Global Options
% 7.78/1.56  
% 7.78/1.56  --schedule                              default
% 7.78/1.56  --add_important_lit                     false
% 7.78/1.56  --prop_solver_per_cl                    1000
% 7.78/1.56  --min_unsat_core                        false
% 7.78/1.56  --soft_assumptions                      false
% 7.78/1.56  --soft_lemma_size                       3
% 7.78/1.56  --prop_impl_unit_size                   0
% 7.78/1.56  --prop_impl_unit                        []
% 7.78/1.56  --share_sel_clauses                     true
% 7.78/1.56  --reset_solvers                         false
% 7.78/1.56  --bc_imp_inh                            [conj_cone]
% 7.78/1.56  --conj_cone_tolerance                   3.
% 7.78/1.56  --extra_neg_conj                        none
% 7.78/1.56  --large_theory_mode                     true
% 7.78/1.56  --prolific_symb_bound                   200
% 7.78/1.56  --lt_threshold                          2000
% 7.78/1.56  --clause_weak_htbl                      true
% 7.78/1.56  --gc_record_bc_elim                     false
% 7.78/1.56  
% 7.78/1.56  ------ Preprocessing Options
% 7.78/1.56  
% 7.78/1.56  --preprocessing_flag                    true
% 7.78/1.56  --time_out_prep_mult                    0.1
% 7.78/1.56  --splitting_mode                        input
% 7.78/1.56  --splitting_grd                         true
% 7.78/1.56  --splitting_cvd                         false
% 7.78/1.56  --splitting_cvd_svl                     false
% 7.78/1.56  --splitting_nvd                         32
% 7.78/1.56  --sub_typing                            true
% 7.78/1.56  --prep_gs_sim                           true
% 7.78/1.56  --prep_unflatten                        true
% 7.78/1.56  --prep_res_sim                          true
% 7.78/1.56  --prep_upred                            true
% 7.78/1.56  --prep_sem_filter                       exhaustive
% 7.78/1.56  --prep_sem_filter_out                   false
% 7.78/1.56  --pred_elim                             true
% 7.78/1.56  --res_sim_input                         true
% 7.78/1.56  --eq_ax_congr_red                       true
% 7.78/1.56  --pure_diseq_elim                       true
% 7.78/1.56  --brand_transform                       false
% 7.78/1.56  --non_eq_to_eq                          false
% 7.78/1.56  --prep_def_merge                        true
% 7.78/1.56  --prep_def_merge_prop_impl              false
% 7.78/1.56  --prep_def_merge_mbd                    true
% 7.78/1.56  --prep_def_merge_tr_red                 false
% 7.78/1.56  --prep_def_merge_tr_cl                  false
% 7.78/1.56  --smt_preprocessing                     true
% 7.78/1.56  --smt_ac_axioms                         fast
% 7.78/1.56  --preprocessed_out                      false
% 7.78/1.56  --preprocessed_stats                    false
% 7.78/1.56  
% 7.78/1.56  ------ Abstraction refinement Options
% 7.78/1.56  
% 7.78/1.56  --abstr_ref                             []
% 7.78/1.56  --abstr_ref_prep                        false
% 7.78/1.56  --abstr_ref_until_sat                   false
% 7.78/1.56  --abstr_ref_sig_restrict                funpre
% 7.78/1.56  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.56  --abstr_ref_under                       []
% 7.78/1.56  
% 7.78/1.56  ------ SAT Options
% 7.78/1.56  
% 7.78/1.56  --sat_mode                              false
% 7.78/1.56  --sat_fm_restart_options                ""
% 7.78/1.56  --sat_gr_def                            false
% 7.78/1.56  --sat_epr_types                         true
% 7.78/1.56  --sat_non_cyclic_types                  false
% 7.78/1.56  --sat_finite_models                     false
% 7.78/1.56  --sat_fm_lemmas                         false
% 7.78/1.56  --sat_fm_prep                           false
% 7.78/1.56  --sat_fm_uc_incr                        true
% 7.78/1.56  --sat_out_model                         small
% 7.78/1.56  --sat_out_clauses                       false
% 7.78/1.56  
% 7.78/1.56  ------ QBF Options
% 7.78/1.56  
% 7.78/1.56  --qbf_mode                              false
% 7.78/1.56  --qbf_elim_univ                         false
% 7.78/1.56  --qbf_dom_inst                          none
% 7.78/1.56  --qbf_dom_pre_inst                      false
% 7.78/1.56  --qbf_sk_in                             false
% 7.78/1.56  --qbf_pred_elim                         true
% 7.78/1.56  --qbf_split                             512
% 7.78/1.56  
% 7.78/1.56  ------ BMC1 Options
% 7.78/1.56  
% 7.78/1.56  --bmc1_incremental                      false
% 7.78/1.56  --bmc1_axioms                           reachable_all
% 7.78/1.56  --bmc1_min_bound                        0
% 7.78/1.56  --bmc1_max_bound                        -1
% 7.78/1.56  --bmc1_max_bound_default                -1
% 7.78/1.56  --bmc1_symbol_reachability              true
% 7.78/1.56  --bmc1_property_lemmas                  false
% 7.78/1.56  --bmc1_k_induction                      false
% 7.78/1.56  --bmc1_non_equiv_states                 false
% 7.78/1.56  --bmc1_deadlock                         false
% 7.78/1.56  --bmc1_ucm                              false
% 7.78/1.56  --bmc1_add_unsat_core                   none
% 7.78/1.56  --bmc1_unsat_core_children              false
% 7.78/1.56  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.56  --bmc1_out_stat                         full
% 7.78/1.56  --bmc1_ground_init                      false
% 7.78/1.56  --bmc1_pre_inst_next_state              false
% 7.78/1.56  --bmc1_pre_inst_state                   false
% 7.78/1.56  --bmc1_pre_inst_reach_state             false
% 7.78/1.56  --bmc1_out_unsat_core                   false
% 7.78/1.56  --bmc1_aig_witness_out                  false
% 7.78/1.56  --bmc1_verbose                          false
% 7.78/1.56  --bmc1_dump_clauses_tptp                false
% 7.78/1.56  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.56  --bmc1_dump_file                        -
% 7.78/1.56  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.56  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.56  --bmc1_ucm_extend_mode                  1
% 7.78/1.56  --bmc1_ucm_init_mode                    2
% 7.78/1.56  --bmc1_ucm_cone_mode                    none
% 7.78/1.56  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.56  --bmc1_ucm_relax_model                  4
% 7.78/1.56  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.56  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.56  --bmc1_ucm_layered_model                none
% 7.78/1.56  --bmc1_ucm_max_lemma_size               10
% 7.78/1.56  
% 7.78/1.56  ------ AIG Options
% 7.78/1.56  
% 7.78/1.56  --aig_mode                              false
% 7.78/1.56  
% 7.78/1.56  ------ Instantiation Options
% 7.78/1.56  
% 7.78/1.56  --instantiation_flag                    true
% 7.78/1.56  --inst_sos_flag                         true
% 7.78/1.56  --inst_sos_phase                        true
% 7.78/1.56  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.56  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.56  --inst_lit_sel_side                     none
% 7.78/1.56  --inst_solver_per_active                1400
% 7.78/1.56  --inst_solver_calls_frac                1.
% 7.78/1.56  --inst_passive_queue_type               priority_queues
% 7.78/1.56  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.56  --inst_passive_queues_freq              [25;2]
% 7.78/1.56  --inst_dismatching                      true
% 7.78/1.56  --inst_eager_unprocessed_to_passive     true
% 7.78/1.56  --inst_prop_sim_given                   true
% 7.78/1.56  --inst_prop_sim_new                     false
% 7.78/1.56  --inst_subs_new                         false
% 7.78/1.56  --inst_eq_res_simp                      false
% 7.78/1.56  --inst_subs_given                       false
% 7.78/1.56  --inst_orphan_elimination               true
% 7.78/1.56  --inst_learning_loop_flag               true
% 7.78/1.56  --inst_learning_start                   3000
% 7.78/1.56  --inst_learning_factor                  2
% 7.78/1.56  --inst_start_prop_sim_after_learn       3
% 7.78/1.56  --inst_sel_renew                        solver
% 7.78/1.56  --inst_lit_activity_flag                true
% 7.78/1.56  --inst_restr_to_given                   false
% 7.78/1.56  --inst_activity_threshold               500
% 7.78/1.56  --inst_out_proof                        true
% 7.78/1.56  
% 7.78/1.56  ------ Resolution Options
% 7.78/1.56  
% 7.78/1.56  --resolution_flag                       false
% 7.78/1.56  --res_lit_sel                           adaptive
% 7.78/1.56  --res_lit_sel_side                      none
% 7.78/1.56  --res_ordering                          kbo
% 7.78/1.56  --res_to_prop_solver                    active
% 7.78/1.56  --res_prop_simpl_new                    false
% 7.78/1.56  --res_prop_simpl_given                  true
% 7.78/1.56  --res_passive_queue_type                priority_queues
% 7.78/1.56  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.56  --res_passive_queues_freq               [15;5]
% 7.78/1.56  --res_forward_subs                      full
% 7.78/1.56  --res_backward_subs                     full
% 7.78/1.56  --res_forward_subs_resolution           true
% 7.78/1.56  --res_backward_subs_resolution          true
% 7.78/1.56  --res_orphan_elimination                true
% 7.78/1.56  --res_time_limit                        2.
% 7.78/1.56  --res_out_proof                         true
% 7.78/1.56  
% 7.78/1.56  ------ Superposition Options
% 7.78/1.56  
% 7.78/1.56  --superposition_flag                    true
% 7.78/1.56  --sup_passive_queue_type                priority_queues
% 7.78/1.56  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.56  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.56  --demod_completeness_check              fast
% 7.78/1.56  --demod_use_ground                      true
% 7.78/1.56  --sup_to_prop_solver                    passive
% 7.78/1.56  --sup_prop_simpl_new                    true
% 7.78/1.56  --sup_prop_simpl_given                  true
% 7.78/1.56  --sup_fun_splitting                     true
% 7.78/1.56  --sup_smt_interval                      50000
% 7.78/1.56  
% 7.78/1.56  ------ Superposition Simplification Setup
% 7.78/1.56  
% 7.78/1.56  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.78/1.56  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.78/1.56  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.56  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.78/1.56  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.56  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.78/1.56  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.78/1.56  --sup_immed_triv                        [TrivRules]
% 7.78/1.56  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.56  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.56  --sup_immed_bw_main                     []
% 7.78/1.56  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.78/1.56  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.56  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.56  --sup_input_bw                          []
% 7.78/1.56  
% 7.78/1.56  ------ Combination Options
% 7.78/1.56  
% 7.78/1.56  --comb_res_mult                         3
% 7.78/1.56  --comb_sup_mult                         2
% 7.78/1.56  --comb_inst_mult                        10
% 7.78/1.56  
% 7.78/1.56  ------ Debug Options
% 7.78/1.56  
% 7.78/1.56  --dbg_backtrace                         false
% 7.78/1.56  --dbg_dump_prop_clauses                 false
% 7.78/1.56  --dbg_dump_prop_clauses_file            -
% 7.78/1.56  --dbg_out_stat                          false
% 7.78/1.56  
% 7.78/1.56  
% 7.78/1.56  
% 7.78/1.56  
% 7.78/1.56  ------ Proving...
% 7.78/1.56  
% 7.78/1.56  
% 7.78/1.56  % SZS status Theorem for theBenchmark.p
% 7.78/1.56  
% 7.78/1.56  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.56  
% 7.78/1.56  fof(f6,axiom,(
% 7.78/1.56    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.78/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.56  
% 7.78/1.56  fof(f13,plain,(
% 7.78/1.56    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.78/1.56    inference(ennf_transformation,[],[f6])).
% 7.78/1.56  
% 7.78/1.56  fof(f26,plain,(
% 7.78/1.56    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 7.78/1.56    introduced(choice_axiom,[])).
% 7.78/1.56  
% 7.78/1.56  fof(f27,plain,(
% 7.78/1.56    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0)))),
% 7.78/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f26])).
% 7.78/1.56  
% 7.78/1.56  fof(f46,plain,(
% 7.78/1.56    ( ! [X0] : (k1_relat_1(sK5(X0)) = X0) )),
% 7.78/1.56    inference(cnf_transformation,[],[f27])).
% 7.78/1.56  
% 7.78/1.56  fof(f5,axiom,(
% 7.78/1.56    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.78/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.56  
% 7.78/1.56  fof(f12,plain,(
% 7.78/1.56    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.78/1.56    inference(ennf_transformation,[],[f5])).
% 7.78/1.56  
% 7.78/1.56  fof(f24,plain,(
% 7.78/1.56    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 7.78/1.56    introduced(choice_axiom,[])).
% 7.78/1.56  
% 7.78/1.56  fof(f25,plain,(
% 7.78/1.56    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 7.78/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f24])).
% 7.78/1.56  
% 7.78/1.56  fof(f42,plain,(
% 7.78/1.56    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 7.78/1.56    inference(cnf_transformation,[],[f25])).
% 7.78/1.56  
% 7.78/1.56  fof(f7,conjecture,(
% 7.78/1.56    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 7.78/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.56  
% 7.78/1.56  fof(f8,negated_conjecture,(
% 7.78/1.56    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 7.78/1.56    inference(negated_conjecture,[],[f7])).
% 7.78/1.56  
% 7.78/1.56  fof(f14,plain,(
% 7.78/1.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 7.78/1.56    inference(ennf_transformation,[],[f8])).
% 7.78/1.56  
% 7.78/1.56  fof(f15,plain,(
% 7.78/1.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.78/1.56    inference(flattening,[],[f14])).
% 7.78/1.56  
% 7.78/1.56  fof(f28,plain,(
% 7.78/1.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK6 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK6 | k1_relat_1(X1) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.78/1.56    introduced(choice_axiom,[])).
% 7.78/1.56  
% 7.78/1.56  fof(f29,plain,(
% 7.78/1.56    k1_xboole_0 != sK6 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK6 | k1_relat_1(X1) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.78/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f28])).
% 7.78/1.56  
% 7.78/1.56  fof(f48,plain,(
% 7.78/1.56    ( ! [X2,X1] : (X1 = X2 | k1_relat_1(X2) != sK6 | k1_relat_1(X1) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.78/1.56    inference(cnf_transformation,[],[f29])).
% 7.78/1.56  
% 7.78/1.56  fof(f40,plain,(
% 7.78/1.56    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 7.78/1.56    inference(cnf_transformation,[],[f25])).
% 7.78/1.56  
% 7.78/1.56  fof(f41,plain,(
% 7.78/1.56    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 7.78/1.56    inference(cnf_transformation,[],[f25])).
% 7.78/1.56  
% 7.78/1.56  fof(f44,plain,(
% 7.78/1.56    ( ! [X0] : (v1_relat_1(sK5(X0))) )),
% 7.78/1.56    inference(cnf_transformation,[],[f27])).
% 7.78/1.56  
% 7.78/1.56  fof(f45,plain,(
% 7.78/1.56    ( ! [X0] : (v1_funct_1(sK5(X0))) )),
% 7.78/1.56    inference(cnf_transformation,[],[f27])).
% 7.78/1.56  
% 7.78/1.56  fof(f4,axiom,(
% 7.78/1.56    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 7.78/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.56  
% 7.78/1.56  fof(f11,plain,(
% 7.78/1.56    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 7.78/1.56    inference(ennf_transformation,[],[f4])).
% 7.78/1.56  
% 7.78/1.56  fof(f18,plain,(
% 7.78/1.56    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.78/1.56    inference(nnf_transformation,[],[f11])).
% 7.78/1.56  
% 7.78/1.56  fof(f19,plain,(
% 7.78/1.56    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.78/1.56    inference(rectify,[],[f18])).
% 7.78/1.56  
% 7.78/1.56  fof(f22,plain,(
% 7.78/1.56    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)))),
% 7.78/1.56    introduced(choice_axiom,[])).
% 7.78/1.56  
% 7.78/1.56  fof(f21,plain,(
% 7.78/1.56    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X3),X0)))) )),
% 7.78/1.56    introduced(choice_axiom,[])).
% 7.78/1.56  
% 7.78/1.56  fof(f20,plain,(
% 7.78/1.56    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.78/1.56    introduced(choice_axiom,[])).
% 7.78/1.56  
% 7.78/1.56  fof(f23,plain,(
% 7.78/1.56    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 7.78/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).
% 7.78/1.56  
% 7.78/1.56  fof(f38,plain,(
% 7.78/1.56    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 7.78/1.56    inference(cnf_transformation,[],[f23])).
% 7.78/1.56  
% 7.78/1.56  fof(f1,axiom,(
% 7.78/1.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.78/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.56  
% 7.78/1.56  fof(f9,plain,(
% 7.78/1.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.78/1.56    inference(rectify,[],[f1])).
% 7.78/1.56  
% 7.78/1.56  fof(f10,plain,(
% 7.78/1.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.78/1.56    inference(ennf_transformation,[],[f9])).
% 7.78/1.56  
% 7.78/1.56  fof(f16,plain,(
% 7.78/1.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.78/1.56    introduced(choice_axiom,[])).
% 7.78/1.56  
% 7.78/1.56  fof(f17,plain,(
% 7.78/1.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.78/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).
% 7.78/1.56  
% 7.78/1.56  fof(f31,plain,(
% 7.78/1.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.78/1.56    inference(cnf_transformation,[],[f17])).
% 7.78/1.56  
% 7.78/1.56  fof(f3,axiom,(
% 7.78/1.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.78/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.56  
% 7.78/1.56  fof(f33,plain,(
% 7.78/1.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.78/1.56    inference(cnf_transformation,[],[f3])).
% 7.78/1.56  
% 7.78/1.56  fof(f2,axiom,(
% 7.78/1.56    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.78/1.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.56  
% 7.78/1.56  fof(f32,plain,(
% 7.78/1.56    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.78/1.56    inference(cnf_transformation,[],[f2])).
% 7.78/1.56  
% 7.78/1.56  fof(f43,plain,(
% 7.78/1.56    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 7.78/1.56    inference(cnf_transformation,[],[f25])).
% 7.78/1.56  
% 7.78/1.56  fof(f37,plain,(
% 7.78/1.56    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 7.78/1.56    inference(cnf_transformation,[],[f23])).
% 7.78/1.56  
% 7.78/1.56  fof(f36,plain,(
% 7.78/1.56    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 7.78/1.56    inference(cnf_transformation,[],[f23])).
% 7.78/1.56  
% 7.78/1.56  fof(f50,plain,(
% 7.78/1.56    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 7.78/1.56    inference(equality_resolution,[],[f36])).
% 7.78/1.56  
% 7.78/1.56  fof(f49,plain,(
% 7.78/1.56    k1_xboole_0 != sK6),
% 7.78/1.56    inference(cnf_transformation,[],[f29])).
% 7.78/1.56  
% 7.78/1.56  fof(f47,plain,(
% 7.78/1.56    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK5(X0),X2) | ~r2_hidden(X2,X0)) )),
% 7.78/1.56    inference(cnf_transformation,[],[f27])).
% 7.78/1.56  
% 7.78/1.56  cnf(c_15,plain,
% 7.78/1.56      ( k1_relat_1(sK5(X0)) = X0 ),
% 7.78/1.56      inference(cnf_transformation,[],[f46]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_11,plain,
% 7.78/1.56      ( k1_relat_1(sK4(X0,X1)) = X0 ),
% 7.78/1.56      inference(cnf_transformation,[],[f42]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_19,negated_conjecture,
% 7.78/1.56      ( ~ v1_funct_1(X0)
% 7.78/1.56      | ~ v1_funct_1(X1)
% 7.78/1.56      | ~ v1_relat_1(X0)
% 7.78/1.56      | ~ v1_relat_1(X1)
% 7.78/1.56      | X1 = X0
% 7.78/1.56      | k1_relat_1(X0) != sK6
% 7.78/1.56      | k1_relat_1(X1) != sK6 ),
% 7.78/1.56      inference(cnf_transformation,[],[f48]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_584,plain,
% 7.78/1.56      ( X0 = X1
% 7.78/1.56      | k1_relat_1(X0) != sK6
% 7.78/1.56      | k1_relat_1(X1) != sK6
% 7.78/1.56      | v1_funct_1(X1) != iProver_top
% 7.78/1.56      | v1_funct_1(X0) != iProver_top
% 7.78/1.56      | v1_relat_1(X1) != iProver_top
% 7.78/1.56      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_944,plain,
% 7.78/1.56      ( sK4(X0,X1) = X2
% 7.78/1.56      | k1_relat_1(X2) != sK6
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | v1_funct_1(X2) != iProver_top
% 7.78/1.56      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 7.78/1.56      | v1_relat_1(X2) != iProver_top
% 7.78/1.56      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_11,c_584]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_13,plain,
% 7.78/1.56      ( v1_relat_1(sK4(X0,X1)) ),
% 7.78/1.56      inference(cnf_transformation,[],[f40]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_33,plain,
% 7.78/1.56      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_12,plain,
% 7.78/1.56      ( v1_funct_1(sK4(X0,X1)) ),
% 7.78/1.56      inference(cnf_transformation,[],[f41]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_36,plain,
% 7.78/1.56      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1098,plain,
% 7.78/1.56      ( v1_relat_1(X2) != iProver_top
% 7.78/1.56      | sK4(X0,X1) = X2
% 7.78/1.56      | k1_relat_1(X2) != sK6
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | v1_funct_1(X2) != iProver_top ),
% 7.78/1.56      inference(global_propositional_subsumption,
% 7.78/1.56                [status(thm)],
% 7.78/1.56                [c_944,c_33,c_36]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1099,plain,
% 7.78/1.56      ( sK4(X0,X1) = X2
% 7.78/1.56      | k1_relat_1(X2) != sK6
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | v1_funct_1(X2) != iProver_top
% 7.78/1.56      | v1_relat_1(X2) != iProver_top ),
% 7.78/1.56      inference(renaming,[status(thm)],[c_1098]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1105,plain,
% 7.78/1.56      ( sK4(X0,X1) = sK5(X2)
% 7.78/1.56      | sK6 != X2
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | v1_funct_1(sK5(X2)) != iProver_top
% 7.78/1.56      | v1_relat_1(sK5(X2)) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_15,c_1099]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_701,plain,
% 7.78/1.56      ( sK5(X0) = X1
% 7.78/1.56      | k1_relat_1(X1) != sK6
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | v1_funct_1(X1) != iProver_top
% 7.78/1.56      | v1_funct_1(sK5(X0)) != iProver_top
% 7.78/1.56      | v1_relat_1(X1) != iProver_top
% 7.78/1.56      | v1_relat_1(sK5(X0)) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_15,c_584]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_17,plain,
% 7.78/1.56      ( v1_relat_1(sK5(X0)) ),
% 7.78/1.56      inference(cnf_transformation,[],[f44]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_23,plain,
% 7.78/1.56      ( v1_relat_1(sK5(X0)) = iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_16,plain,
% 7.78/1.56      ( v1_funct_1(sK5(X0)) ),
% 7.78/1.56      inference(cnf_transformation,[],[f45]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_26,plain,
% 7.78/1.56      ( v1_funct_1(sK5(X0)) = iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_813,plain,
% 7.78/1.56      ( v1_relat_1(X1) != iProver_top
% 7.78/1.56      | sK5(X0) = X1
% 7.78/1.56      | k1_relat_1(X1) != sK6
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | v1_funct_1(X1) != iProver_top ),
% 7.78/1.56      inference(global_propositional_subsumption,
% 7.78/1.56                [status(thm)],
% 7.78/1.56                [c_701,c_23,c_26]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_814,plain,
% 7.78/1.56      ( sK5(X0) = X1
% 7.78/1.56      | k1_relat_1(X1) != sK6
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | v1_funct_1(X1) != iProver_top
% 7.78/1.56      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.56      inference(renaming,[status(thm)],[c_813]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_943,plain,
% 7.78/1.56      ( sK4(X0,X1) = sK5(X2)
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | sK6 != X2
% 7.78/1.56      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 7.78/1.56      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_11,c_814]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_945,plain,
% 7.78/1.56      ( ~ v1_funct_1(sK4(X0,X1))
% 7.78/1.56      | ~ v1_relat_1(sK4(X0,X1))
% 7.78/1.56      | sK4(X0,X1) = sK5(X2)
% 7.78/1.56      | sK6 != X0
% 7.78/1.56      | sK6 != X2 ),
% 7.78/1.56      inference(predicate_to_equality_rev,[status(thm)],[c_943]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1113,plain,
% 7.78/1.56      ( sK4(X0,X1) = sK5(X2) | sK6 != X2 | sK6 != X0 ),
% 7.78/1.56      inference(global_propositional_subsumption,
% 7.78/1.56                [status(thm)],
% 7.78/1.56                [c_1105,c_13,c_12,c_945]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1114,plain,
% 7.78/1.56      ( sK4(X0,X1) = sK5(X2) | sK6 != X0 | sK6 != X2 ),
% 7.78/1.56      inference(renaming,[status(thm)],[c_1113]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1116,plain,
% 7.78/1.56      ( sK4(sK6,X0) = sK5(X1) | sK6 != X1 ),
% 7.78/1.56      inference(equality_resolution,[status(thm)],[c_1114]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1160,plain,
% 7.78/1.56      ( sK4(sK6,X0) = sK5(sK6) ),
% 7.78/1.56      inference(equality_resolution,[status(thm)],[c_1116]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_5,plain,
% 7.78/1.56      ( r2_hidden(sK2(X0,X1,X2),X1)
% 7.78/1.56      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.78/1.56      | ~ v1_relat_1(X0)
% 7.78/1.56      | k9_relat_1(X0,X1) = X2 ),
% 7.78/1.56      inference(cnf_transformation,[],[f38]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_595,plain,
% 7.78/1.56      ( k9_relat_1(X0,X1) = X2
% 7.78/1.56      | r2_hidden(sK2(X0,X1,X2),X1) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 7.78/1.56      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_588,plain,
% 7.78/1.56      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_0,plain,
% 7.78/1.56      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.78/1.56      inference(cnf_transformation,[],[f31]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_3,plain,
% 7.78/1.56      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.78/1.56      inference(cnf_transformation,[],[f33]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_208,plain,
% 7.78/1.56      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 7.78/1.56      | X3 != X1
% 7.78/1.56      | k1_xboole_0 != X2 ),
% 7.78/1.56      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_209,plain,
% 7.78/1.56      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 7.78/1.56      inference(unflattening,[status(thm)],[c_208]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_582,plain,
% 7.78/1.56      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_2,plain,
% 7.78/1.56      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.78/1.56      inference(cnf_transformation,[],[f32]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_597,plain,
% 7.78/1.56      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.78/1.56      inference(demodulation,[status(thm)],[c_582,c_2]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1967,plain,
% 7.78/1.56      ( k9_relat_1(X0,X1) = k1_xboole_0
% 7.78/1.56      | r2_hidden(sK2(X0,X1,k1_xboole_0),X1) = iProver_top
% 7.78/1.56      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_595,c_597]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_10,plain,
% 7.78/1.56      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK4(X1,X2),X0) = X2 ),
% 7.78/1.56      inference(cnf_transformation,[],[f43]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_590,plain,
% 7.78/1.56      ( k1_funct_1(sK4(X0,X1),X2) = X1
% 7.78/1.56      | r2_hidden(X2,X0) != iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_2610,plain,
% 7.78/1.56      ( k1_funct_1(sK4(X0,X1),sK2(X2,X0,k1_xboole_0)) = X1
% 7.78/1.56      | k9_relat_1(X2,X0) = k1_xboole_0
% 7.78/1.56      | v1_relat_1(X2) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_1967,c_590]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_4737,plain,
% 7.78/1.56      ( k1_funct_1(sK4(X0,X1),sK2(sK4(X2,X3),X0,k1_xboole_0)) = X1
% 7.78/1.56      | k9_relat_1(sK4(X2,X3),X0) = k1_xboole_0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_588,c_2610]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_4799,plain,
% 7.78/1.56      ( k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0)) = X2
% 7.78/1.56      | k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_1160,c_4737]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_5007,plain,
% 7.78/1.56      ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
% 7.78/1.56      | k1_relat_1(k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0))) = X2 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_4799,c_11]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_5676,plain,
% 7.78/1.56      ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
% 7.78/1.56      | k1_relat_1(k1_relat_1(k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0)))) = X2 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_5007,c_11]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_5895,plain,
% 7.78/1.56      ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
% 7.78/1.56      | k1_relat_1(k1_relat_1(k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0)))) = k1_xboole_0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_5676,c_2]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_6115,plain,
% 7.78/1.56      ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
% 7.78/1.56      | k1_relat_1(X2) = k1_xboole_0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_5007,c_5895]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_5783,plain,
% 7.78/1.56      ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0 | k1_relat_1(X2) = X3 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_5007,c_5676]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_11592,plain,
% 7.78/1.56      ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
% 7.78/1.56      | k1_relat_1(X2) != k1_xboole_0 ),
% 7.78/1.56      inference(equality_factoring,[status(thm)],[c_5783]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_11635,plain,
% 7.78/1.56      ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0 ),
% 7.78/1.56      inference(global_propositional_subsumption,
% 7.78/1.56                [status(thm)],
% 7.78/1.56                [c_6115,c_11592]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_11648,plain,
% 7.78/1.56      ( k9_relat_1(sK5(sK6),sK6) = k1_xboole_0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_1160,c_11635]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_6,plain,
% 7.78/1.56      ( r2_hidden(sK1(X0,X1,X2),X2)
% 7.78/1.56      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0)
% 7.78/1.56      | ~ v1_relat_1(X0)
% 7.78/1.56      | k9_relat_1(X0,X1) = X2 ),
% 7.78/1.56      inference(cnf_transformation,[],[f37]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_594,plain,
% 7.78/1.56      ( k9_relat_1(X0,X1) = X2
% 7.78/1.56      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 7.78/1.56      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0) = iProver_top
% 7.78/1.56      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_7,plain,
% 7.78/1.56      ( ~ r2_hidden(X0,X1)
% 7.78/1.56      | r2_hidden(X2,k9_relat_1(X3,X1))
% 7.78/1.56      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 7.78/1.56      | ~ v1_relat_1(X3) ),
% 7.78/1.56      inference(cnf_transformation,[],[f50]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_593,plain,
% 7.78/1.56      ( r2_hidden(X0,X1) != iProver_top
% 7.78/1.56      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 7.78/1.56      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 7.78/1.56      | v1_relat_1(X3) != iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1922,plain,
% 7.78/1.56      ( k9_relat_1(X0,X1) = X2
% 7.78/1.56      | r2_hidden(sK2(X0,X1,X2),X3) != iProver_top
% 7.78/1.56      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(X0,X1,X2),k9_relat_1(X0,X3)) = iProver_top
% 7.78/1.56      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_594,c_593]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_14696,plain,
% 7.78/1.56      ( k9_relat_1(sK5(sK6),X0) = X1
% 7.78/1.56      | r2_hidden(sK2(sK5(sK6),X0,X1),sK6) != iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),X0,X1),X1) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),X0,X1),k1_xboole_0) = iProver_top
% 7.78/1.56      | v1_relat_1(sK5(sK6)) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_11648,c_1922]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1238,plain,
% 7.78/1.56      ( v1_relat_1(sK5(sK6)) ),
% 7.78/1.56      inference(instantiation,[status(thm)],[c_17]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_1239,plain,
% 7.78/1.56      ( v1_relat_1(sK5(sK6)) = iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_16368,plain,
% 7.78/1.56      ( r2_hidden(sK1(sK5(sK6),X0,X1),k1_xboole_0) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),X0,X1),X1) = iProver_top
% 7.78/1.56      | r2_hidden(sK2(sK5(sK6),X0,X1),sK6) != iProver_top
% 7.78/1.56      | k9_relat_1(sK5(sK6),X0) = X1 ),
% 7.78/1.56      inference(global_propositional_subsumption,
% 7.78/1.56                [status(thm)],
% 7.78/1.56                [c_14696,c_1239]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_16369,plain,
% 7.78/1.56      ( k9_relat_1(sK5(sK6),X0) = X1
% 7.78/1.56      | r2_hidden(sK2(sK5(sK6),X0,X1),sK6) != iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),X0,X1),X1) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),X0,X1),k1_xboole_0) = iProver_top ),
% 7.78/1.56      inference(renaming,[status(thm)],[c_16368]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_16374,plain,
% 7.78/1.56      ( k9_relat_1(sK5(sK6),sK6) = X0
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),sK6,X0),k1_xboole_0) = iProver_top
% 7.78/1.56      | v1_relat_1(sK5(sK6)) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_595,c_16369]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_16394,plain,
% 7.78/1.56      ( k1_xboole_0 = X0
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),sK6,X0),k1_xboole_0) = iProver_top
% 7.78/1.56      | v1_relat_1(sK5(sK6)) != iProver_top ),
% 7.78/1.56      inference(demodulation,[status(thm)],[c_16374,c_11648]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_17127,plain,
% 7.78/1.56      ( r2_hidden(sK1(sK5(sK6),sK6,X0),k1_xboole_0) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top
% 7.78/1.56      | k1_xboole_0 = X0 ),
% 7.78/1.56      inference(global_propositional_subsumption,
% 7.78/1.56                [status(thm)],
% 7.78/1.56                [c_16394,c_1239]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_17128,plain,
% 7.78/1.56      ( k1_xboole_0 = X0
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),sK6,X0),k1_xboole_0) = iProver_top ),
% 7.78/1.56      inference(renaming,[status(thm)],[c_17127]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_17151,plain,
% 7.78/1.56      ( k1_xboole_0 = X0
% 7.78/1.56      | r2_hidden(sK1(sK5(sK6),sK6,X0),X0) = iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_17128,c_597]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_17392,plain,
% 7.78/1.56      ( k1_funct_1(sK4(X0,X1),sK1(sK5(sK6),sK6,X0)) = X1
% 7.78/1.56      | k1_xboole_0 = X0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_17151,c_590]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_17691,plain,
% 7.78/1.56      ( k1_funct_1(sK5(sK6),sK1(sK5(sK6),sK6,sK6)) = X0
% 7.78/1.56      | sK6 = k1_xboole_0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_1160,c_17392]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_18,negated_conjecture,
% 7.78/1.56      ( k1_xboole_0 != sK6 ),
% 7.78/1.56      inference(cnf_transformation,[],[f49]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_326,plain,( X0 = X0 ),theory(equality) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_343,plain,
% 7.78/1.56      ( k1_xboole_0 = k1_xboole_0 ),
% 7.78/1.56      inference(instantiation,[status(thm)],[c_326]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_327,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_616,plain,
% 7.78/1.56      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 7.78/1.56      inference(instantiation,[status(thm)],[c_327]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_617,plain,
% 7.78/1.56      ( sK6 != k1_xboole_0
% 7.78/1.56      | k1_xboole_0 = sK6
% 7.78/1.56      | k1_xboole_0 != k1_xboole_0 ),
% 7.78/1.56      inference(instantiation,[status(thm)],[c_616]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_17701,plain,
% 7.78/1.56      ( k1_funct_1(sK5(sK6),sK1(sK5(sK6),sK6,sK6)) = X0 ),
% 7.78/1.56      inference(global_propositional_subsumption,
% 7.78/1.56                [status(thm)],
% 7.78/1.56                [c_17691,c_18,c_343,c_617]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_17770,plain,
% 7.78/1.56      ( X0 = X1 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_17701,c_17701]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_14,plain,
% 7.78/1.56      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK5(X1),X0) = k1_xboole_0 ),
% 7.78/1.56      inference(cnf_transformation,[],[f47]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_587,plain,
% 7.78/1.56      ( k1_funct_1(sK5(X0),X1) = k1_xboole_0
% 7.78/1.56      | r2_hidden(X1,X0) != iProver_top ),
% 7.78/1.56      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_2611,plain,
% 7.78/1.56      ( k1_funct_1(sK5(X0),sK2(X1,X0,k1_xboole_0)) = k1_xboole_0
% 7.78/1.56      | k9_relat_1(X1,X0) = k1_xboole_0
% 7.78/1.56      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_1967,c_587]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_3433,plain,
% 7.78/1.56      ( k1_funct_1(sK5(X0),sK2(sK4(X1,X2),X0,k1_xboole_0)) = k1_xboole_0
% 7.78/1.56      | k9_relat_1(sK4(X1,X2),X0) = k1_xboole_0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_588,c_2611]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_4988,plain,
% 7.78/1.56      ( k1_funct_1(sK5(sK6),sK2(sK4(X0,X1),sK6,k1_xboole_0)) != sK6
% 7.78/1.56      | k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
% 7.78/1.56      | sK5(X2) = X3
% 7.78/1.56      | sK6 != X2
% 7.78/1.56      | v1_funct_1(X3) != iProver_top
% 7.78/1.56      | v1_relat_1(X3) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_4799,c_814]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_5401,plain,
% 7.78/1.56      ( k9_relat_1(sK4(X0,X1),sK6) = k1_xboole_0
% 7.78/1.56      | sK5(X2) = X3
% 7.78/1.56      | sK6 != X2
% 7.78/1.56      | sK6 != k1_xboole_0
% 7.78/1.56      | v1_funct_1(X3) != iProver_top
% 7.78/1.56      | v1_relat_1(X3) != iProver_top ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_3433,c_4988]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_5478,plain,
% 7.78/1.56      ( sK6 != k1_xboole_0 ),
% 7.78/1.56      inference(global_propositional_subsumption,
% 7.78/1.56                [status(thm)],
% 7.78/1.56                [c_5401,c_18,c_343,c_617]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_18262,plain,
% 7.78/1.56      ( k1_xboole_0 != X0 ),
% 7.78/1.56      inference(superposition,[status(thm)],[c_17770,c_5478]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(c_18265,plain,
% 7.78/1.56      ( k1_xboole_0 != k1_xboole_0 ),
% 7.78/1.56      inference(instantiation,[status(thm)],[c_18262]) ).
% 7.78/1.56  
% 7.78/1.56  cnf(contradiction,plain,
% 7.78/1.56      ( $false ),
% 7.78/1.56      inference(minisat,[status(thm)],[c_18265,c_343]) ).
% 7.78/1.56  
% 7.78/1.56  
% 7.78/1.56  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.56  
% 7.78/1.56  ------                               Statistics
% 7.78/1.56  
% 7.78/1.56  ------ General
% 7.78/1.56  
% 7.78/1.56  abstr_ref_over_cycles:                  0
% 7.78/1.56  abstr_ref_under_cycles:                 0
% 7.78/1.56  gc_basic_clause_elim:                   0
% 7.78/1.56  forced_gc_time:                         0
% 7.78/1.56  parsing_time:                           0.021
% 7.78/1.56  unif_index_cands_time:                  0.
% 7.78/1.56  unif_index_add_time:                    0.
% 7.78/1.56  orderings_time:                         0.
% 7.78/1.56  out_proof_time:                         0.014
% 7.78/1.56  total_time:                             0.741
% 7.78/1.56  num_of_symbols:                         49
% 7.78/1.56  num_of_terms:                           32645
% 7.78/1.56  
% 7.78/1.56  ------ Preprocessing
% 7.78/1.56  
% 7.78/1.56  num_of_splits:                          0
% 7.78/1.56  num_of_split_atoms:                     1
% 7.78/1.56  num_of_reused_defs:                     1
% 7.78/1.56  num_eq_ax_congr_red:                    55
% 7.78/1.56  num_of_sem_filtered_clauses:            1
% 7.78/1.56  num_of_subtypes:                        0
% 7.78/1.56  monotx_restored_types:                  0
% 7.78/1.56  sat_num_of_epr_types:                   0
% 7.78/1.56  sat_num_of_non_cyclic_types:            0
% 7.78/1.56  sat_guarded_non_collapsed_types:        0
% 7.78/1.56  num_pure_diseq_elim:                    0
% 7.78/1.56  simp_replaced_by:                       0
% 7.78/1.56  res_preprocessed:                       96
% 7.78/1.56  prep_upred:                             0
% 7.78/1.56  prep_unflattend:                        4
% 7.78/1.56  smt_new_axioms:                         0
% 7.78/1.56  pred_elim_cands:                        3
% 7.78/1.56  pred_elim:                              1
% 7.78/1.56  pred_elim_cl:                           1
% 7.78/1.56  pred_elim_cycles:                       3
% 7.78/1.56  merged_defs:                            0
% 7.78/1.56  merged_defs_ncl:                        0
% 7.78/1.56  bin_hyper_res:                          0
% 7.78/1.56  prep_cycles:                            4
% 7.78/1.56  pred_elim_time:                         0.012
% 7.78/1.56  splitting_time:                         0.
% 7.78/1.56  sem_filter_time:                        0.
% 7.78/1.56  monotx_time:                            0.
% 7.78/1.56  subtype_inf_time:                       0.
% 7.78/1.56  
% 7.78/1.56  ------ Problem properties
% 7.78/1.56  
% 7.78/1.56  clauses:                                19
% 7.78/1.56  conjectures:                            2
% 7.78/1.56  epr:                                    1
% 7.78/1.56  horn:                                   17
% 7.78/1.56  ground:                                 1
% 7.78/1.56  unary:                                  9
% 7.78/1.56  binary:                                 3
% 7.78/1.56  lits:                                   45
% 7.78/1.56  lits_eq:                                12
% 7.78/1.56  fd_pure:                                0
% 7.78/1.56  fd_pseudo:                              0
% 7.78/1.56  fd_cond:                                0
% 7.78/1.56  fd_pseudo_cond:                         4
% 7.78/1.56  ac_symbols:                             0
% 7.78/1.56  
% 7.78/1.56  ------ Propositional Solver
% 7.78/1.56  
% 7.78/1.56  prop_solver_calls:                      34
% 7.78/1.56  prop_fast_solver_calls:                 1903
% 7.78/1.56  smt_solver_calls:                       0
% 7.78/1.56  smt_fast_solver_calls:                  0
% 7.78/1.56  prop_num_of_clauses:                    7948
% 7.78/1.56  prop_preprocess_simplified:             14387
% 7.78/1.56  prop_fo_subsumed:                       244
% 7.78/1.56  prop_solver_time:                       0.
% 7.78/1.56  smt_solver_time:                        0.
% 7.78/1.56  smt_fast_solver_time:                   0.
% 7.78/1.56  prop_fast_solver_time:                  0.
% 7.78/1.56  prop_unsat_core_time:                   0.
% 7.78/1.56  
% 7.78/1.56  ------ QBF
% 7.78/1.56  
% 7.78/1.56  qbf_q_res:                              0
% 7.78/1.56  qbf_num_tautologies:                    0
% 7.78/1.56  qbf_prep_cycles:                        0
% 7.78/1.56  
% 7.78/1.56  ------ BMC1
% 7.78/1.56  
% 7.78/1.56  bmc1_current_bound:                     -1
% 7.78/1.56  bmc1_last_solved_bound:                 -1
% 7.78/1.56  bmc1_unsat_core_size:                   -1
% 7.78/1.56  bmc1_unsat_core_parents_size:           -1
% 7.78/1.56  bmc1_merge_next_fun:                    0
% 7.78/1.56  bmc1_unsat_core_clauses_time:           0.
% 7.78/1.56  
% 7.78/1.56  ------ Instantiation
% 7.78/1.56  
% 7.78/1.56  inst_num_of_clauses:                    1861
% 7.78/1.56  inst_num_in_passive:                    421
% 7.78/1.56  inst_num_in_active:                     801
% 7.78/1.56  inst_num_in_unprocessed:                645
% 7.78/1.56  inst_num_of_loops:                      910
% 7.78/1.56  inst_num_of_learning_restarts:          0
% 7.78/1.56  inst_num_moves_active_passive:          103
% 7.78/1.56  inst_lit_activity:                      0
% 7.78/1.56  inst_lit_activity_moves:                0
% 7.78/1.56  inst_num_tautologies:                   0
% 7.78/1.56  inst_num_prop_implied:                  0
% 7.78/1.56  inst_num_existing_simplified:           0
% 7.78/1.56  inst_num_eq_res_simplified:             0
% 7.78/1.56  inst_num_child_elim:                    0
% 7.78/1.56  inst_num_of_dismatching_blockings:      1860
% 7.78/1.56  inst_num_of_non_proper_insts:           2510
% 7.78/1.56  inst_num_of_duplicates:                 0
% 7.78/1.56  inst_inst_num_from_inst_to_res:         0
% 7.78/1.56  inst_dismatching_checking_time:         0.
% 7.78/1.56  
% 7.78/1.56  ------ Resolution
% 7.78/1.56  
% 7.78/1.56  res_num_of_clauses:                     0
% 7.78/1.56  res_num_in_passive:                     0
% 7.78/1.56  res_num_in_active:                      0
% 7.78/1.56  res_num_of_loops:                       100
% 7.78/1.56  res_forward_subset_subsumed:            339
% 7.78/1.56  res_backward_subset_subsumed:           28
% 7.78/1.56  res_forward_subsumed:                   0
% 7.78/1.56  res_backward_subsumed:                  0
% 7.78/1.56  res_forward_subsumption_resolution:     0
% 7.78/1.56  res_backward_subsumption_resolution:    0
% 7.78/1.56  res_clause_to_clause_subsumption:       7492
% 7.78/1.56  res_orphan_elimination:                 0
% 7.78/1.56  res_tautology_del:                      138
% 7.78/1.56  res_num_eq_res_simplified:              0
% 7.78/1.56  res_num_sel_changes:                    0
% 7.78/1.56  res_moves_from_active_to_pass:          0
% 7.78/1.56  
% 7.78/1.56  ------ Superposition
% 7.78/1.56  
% 7.78/1.56  sup_time_total:                         0.
% 7.78/1.56  sup_time_generating:                    0.
% 7.78/1.56  sup_time_sim_full:                      0.
% 7.78/1.56  sup_time_sim_immed:                     0.
% 7.78/1.56  
% 7.78/1.56  sup_num_of_clauses:                     913
% 7.78/1.56  sup_num_in_active:                      4
% 7.78/1.56  sup_num_in_passive:                     909
% 7.78/1.56  sup_num_of_loops:                       180
% 7.78/1.56  sup_fw_superposition:                   1443
% 7.78/1.56  sup_bw_superposition:                   2158
% 7.78/1.56  sup_immediate_simplified:               1274
% 7.78/1.56  sup_given_eliminated:                   20
% 7.78/1.56  comparisons_done:                       0
% 7.78/1.56  comparisons_avoided:                    62
% 7.78/1.56  
% 7.78/1.56  ------ Simplifications
% 7.78/1.56  
% 7.78/1.56  
% 7.78/1.56  sim_fw_subset_subsumed:                 299
% 7.78/1.56  sim_bw_subset_subsumed:                 309
% 7.78/1.56  sim_fw_subsumed:                        1279
% 7.78/1.56  sim_bw_subsumed:                        270
% 7.78/1.56  sim_fw_subsumption_res:                 0
% 7.78/1.56  sim_bw_subsumption_res:                 0
% 7.78/1.56  sim_tautology_del:                      2
% 7.78/1.56  sim_eq_tautology_del:                   82
% 7.78/1.56  sim_eq_res_simp:                        1
% 7.78/1.56  sim_fw_demodulated:                     127
% 7.78/1.56  sim_bw_demodulated:                     217
% 7.78/1.56  sim_light_normalised:                   68
% 7.78/1.56  sim_joinable_taut:                      0
% 7.78/1.56  sim_joinable_simp:                      0
% 7.78/1.56  sim_ac_normalised:                      0
% 7.78/1.56  sim_smt_subsumption:                    0
% 7.78/1.56  
%------------------------------------------------------------------------------

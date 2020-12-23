%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:19 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  115 (2182 expanded)
%              Number of clauses        :   78 (1048 expanded)
%              Number of leaves         :   13 ( 427 expanded)
%              Depth                    :   27
%              Number of atoms          :  469 (7559 expanded)
%              Number of equality atoms :  249 (2521 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f12,f23])).

fof(f38,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f28,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f31,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f39,plain,
    ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_208,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_483,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_222,plain,
    ( r1_tarski(k1_xboole_0,X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_471,plain,
    ( r1_tarski(k1_xboole_0,X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_215,plain,
    ( r2_hidden(k4_tarski(sK4(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X1_44)
    | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X2_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X2_44)
    | ~ v1_relat_1(X1_44)
    | k5_relat_1(X0_44,X1_44) = X2_44 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_477,plain,
    ( k5_relat_1(X0_44,X1_44) = X2_44
    | r2_hidden(k4_tarski(sK4(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X1_44) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X2_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X2_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X0,X1),X3)
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_217,plain,
    ( ~ r2_hidden(k4_tarski(X0_47,X1_47),X0_44)
    | r2_hidden(k4_tarski(X0_47,X1_47),X1_44)
    | ~ r1_tarski(X0_44,X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_475,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),X0_44) != iProver_top
    | r2_hidden(k4_tarski(X0_47,X1_47),X1_44) = iProver_top
    | r1_tarski(X0_44,X1_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_1656,plain,
    ( k5_relat_1(X0_44,X1_44) = X2_44
    | r2_hidden(k4_tarski(sK4(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X1_44) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X3_44) = iProver_top
    | r1_tarski(X2_44,X3_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X2_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_477,c_475])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0_46,k2_zfmisc_1(X0_46,X0_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_472,plain,
    ( r2_hidden(X0_46,k2_zfmisc_1(X0_46,X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_7286,plain,
    ( k5_relat_1(X0_44,X1_44) = X2_44
    | r2_hidden(k4_tarski(sK4(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X1_44) = iProver_top
    | r1_tarski(X2_44,k2_zfmisc_1(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X0_48)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X2_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_1656,c_472])).

cnf(c_7368,plain,
    ( k5_relat_1(X0_44,X1_44) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X1_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_471,c_7286])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_221,plain,
    ( k4_xboole_0(X0_44,k2_xboole_0(X0_44,X0_49)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_210,plain,
    ( ~ v1_relat_1(X0_44)
    | v1_relat_1(k4_xboole_0(X0_44,X0_45)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_482,plain,
    ( v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k4_xboole_0(X0_44,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_629,plain,
    ( v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_221,c_482])).

cnf(c_684,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_629])).

cnf(c_7765,plain,
    ( v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | r2_hidden(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X1_44) = iProver_top
    | k5_relat_1(X0_44,X1_44) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7368,c_684])).

cnf(c_7766,plain,
    ( k5_relat_1(X0_44,X1_44) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X1_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(renaming,[status(thm)],[c_7765])).

cnf(c_7776,plain,
    ( k5_relat_1(X0_44,X1_44) = k1_xboole_0
    | r2_hidden(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X2_44) = iProver_top
    | r1_tarski(X1_44,X2_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_7766,c_475])).

cnf(c_9033,plain,
    ( k5_relat_1(X0_44,X1_44) = k1_xboole_0
    | r1_tarski(X1_44,k2_zfmisc_1(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X0_48)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_7776,c_472])).

cnf(c_9078,plain,
    ( k5_relat_1(X0_44,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_471,c_9033])).

cnf(c_9232,plain,
    ( v1_relat_1(X0_44) != iProver_top
    | k5_relat_1(X0_44,k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9078,c_684])).

cnf(c_9233,plain,
    ( k5_relat_1(X0_44,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top ),
    inference(renaming,[status(thm)],[c_9232])).

cnf(c_9236,plain,
    ( k5_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_483,c_9233])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_214,plain,
    ( r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK4(X0_44,X1_44,X2_44)),X0_44)
    | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X2_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X2_44)
    | ~ v1_relat_1(X1_44)
    | k5_relat_1(X0_44,X1_44) = X2_44 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_478,plain,
    ( k5_relat_1(X0_44,X1_44) = X2_44
    | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK4(X0_44,X1_44,X2_44)),X0_44) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X2_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X2_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_212,plain,
    ( ~ r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44))
    | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_47,X1_47),X1_47),X1_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_480,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_47,X1_47),X1_47),X1_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_840,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_47,X1_47),X1_47),X2_44) = iProver_top
    | r1_tarski(X1_44,X2_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_480,c_475])).

cnf(c_1113,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
    | r1_tarski(X1_44,k2_zfmisc_1(k4_tarski(sK5(X0_44,X1_44,X0_47,X1_47),X1_47),X0_48)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_472])).

cnf(c_1195,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_471,c_1113])).

cnf(c_1200,plain,
    ( v1_relat_1(k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1195,c_684])).

cnf(c_1201,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1200])).

cnf(c_1693,plain,
    ( k5_relat_1(X0_44,X1_44) = k5_relat_1(X2_44,k1_xboole_0)
    | r2_hidden(k4_tarski(sK2(X0_44,X1_44,k5_relat_1(X2_44,k1_xboole_0)),sK4(X0_44,X1_44,k5_relat_1(X2_44,k1_xboole_0))),X0_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X2_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X2_44,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_478,c_1201])).

cnf(c_4692,plain,
    ( k5_relat_1(k5_relat_1(X0_44,k1_xboole_0),X1_44) = k5_relat_1(X2_44,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X2_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(X2_44,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_1201])).

cnf(c_9258,plain,
    ( k5_relat_1(k5_relat_1(sK6,k1_xboole_0),X0_44) = k5_relat_1(X1_44,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9236,c_4692])).

cnf(c_9307,plain,
    ( k5_relat_1(k1_xboole_0,X0_44) = k5_relat_1(X1_44,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9258,c_9236])).

cnf(c_9237,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_684,c_9233])).

cnf(c_9588,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X0_44) = k5_relat_1(X1_44,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9237,c_4692])).

cnf(c_9664,plain,
    ( k5_relat_1(k1_xboole_0,X0_44) = k5_relat_1(X1_44,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9588,c_9237])).

cnf(c_10136,plain,
    ( k5_relat_1(k1_xboole_0,X0_44) = k5_relat_1(X1_44,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9307,c_684,c_9664])).

cnf(c_10140,plain,
    ( k5_relat_1(k1_xboole_0,X0_44) = k5_relat_1(sK6,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9236,c_10136])).

cnf(c_10143,plain,
    ( k5_relat_1(k1_xboole_0,X0_44) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10140,c_9236])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_211,plain,
    ( ~ r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44))
    | r2_hidden(k4_tarski(X0_47,sK5(X0_44,X1_44,X0_47,X1_47)),X0_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | ~ v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_481,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
    | r2_hidden(k4_tarski(X0_47,sK5(X0_44,X1_44,X0_47,X1_47)),X0_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_994,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
    | r2_hidden(k4_tarski(X0_47,sK5(X0_44,X1_44,X0_47,X1_47)),X2_44) = iProver_top
    | r1_tarski(X0_44,X2_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_481,c_475])).

cnf(c_2078,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
    | r1_tarski(X0_44,k2_zfmisc_1(k4_tarski(X0_47,sK5(X0_44,X1_44,X0_47,X1_47)),X0_48)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_472])).

cnf(c_2206,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_471,c_2078])).

cnf(c_2212,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(k1_xboole_0,X0_44)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2206,c_684])).

cnf(c_2213,plain,
    ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2212])).

cnf(c_4695,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k5_relat_1(X2_44,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X2_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(X2_44,k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1693,c_2213])).

cnf(c_9277,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k5_relat_1(sK6,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9236,c_4695])).

cnf(c_9291,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9277,c_9236])).

cnf(c_9607,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9237,c_4695])).

cnf(c_9661,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9607,c_9237])).

cnf(c_9853,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9291,c_684,c_9661])).

cnf(c_9857,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X0_44) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9237,c_9853])).

cnf(c_9858,plain,
    ( k5_relat_1(k1_xboole_0,X0_44) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9857,c_9237])).

cnf(c_10146,plain,
    ( k5_relat_1(k1_xboole_0,X0_44) = k1_xboole_0
    | v1_relat_1(X0_44) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10143,c_684,c_9858])).

cnf(c_10150,plain,
    ( k5_relat_1(k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_483,c_10146])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_209,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_9242,plain,
    ( k5_relat_1(k1_xboole_0,sK6) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9236,c_209])).

cnf(c_224,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_242,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10150,c_9242,c_242])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:20:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.01/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.98  
% 4.01/0.98  ------  iProver source info
% 4.01/0.98  
% 4.01/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.98  git: non_committed_changes: false
% 4.01/0.98  git: last_make_outside_of_git: false
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options
% 4.01/0.98  
% 4.01/0.98  --out_options                           all
% 4.01/0.98  --tptp_safe_out                         true
% 4.01/0.98  --problem_path                          ""
% 4.01/0.98  --include_path                          ""
% 4.01/0.98  --clausifier                            res/vclausify_rel
% 4.01/0.98  --clausifier_options                    ""
% 4.01/0.98  --stdin                                 false
% 4.01/0.98  --stats_out                             all
% 4.01/0.98  
% 4.01/0.98  ------ General Options
% 4.01/0.98  
% 4.01/0.98  --fof                                   false
% 4.01/0.98  --time_out_real                         305.
% 4.01/0.98  --time_out_virtual                      -1.
% 4.01/0.98  --symbol_type_check                     false
% 4.01/0.98  --clausify_out                          false
% 4.01/0.98  --sig_cnt_out                           false
% 4.01/0.98  --trig_cnt_out                          false
% 4.01/0.98  --trig_cnt_out_tolerance                1.
% 4.01/0.98  --trig_cnt_out_sk_spl                   false
% 4.01/0.98  --abstr_cl_out                          false
% 4.01/0.98  
% 4.01/0.98  ------ Global Options
% 4.01/0.98  
% 4.01/0.98  --schedule                              default
% 4.01/0.98  --add_important_lit                     false
% 4.01/0.98  --prop_solver_per_cl                    1000
% 4.01/0.98  --min_unsat_core                        false
% 4.01/0.98  --soft_assumptions                      false
% 4.01/0.98  --soft_lemma_size                       3
% 4.01/0.98  --prop_impl_unit_size                   0
% 4.01/0.98  --prop_impl_unit                        []
% 4.01/0.98  --share_sel_clauses                     true
% 4.01/0.98  --reset_solvers                         false
% 4.01/0.98  --bc_imp_inh                            [conj_cone]
% 4.01/0.98  --conj_cone_tolerance                   3.
% 4.01/0.98  --extra_neg_conj                        none
% 4.01/0.98  --large_theory_mode                     true
% 4.01/0.98  --prolific_symb_bound                   200
% 4.01/0.98  --lt_threshold                          2000
% 4.01/0.98  --clause_weak_htbl                      true
% 4.01/0.98  --gc_record_bc_elim                     false
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing Options
% 4.01/0.98  
% 4.01/0.98  --preprocessing_flag                    true
% 4.01/0.98  --time_out_prep_mult                    0.1
% 4.01/0.98  --splitting_mode                        input
% 4.01/0.98  --splitting_grd                         true
% 4.01/0.98  --splitting_cvd                         false
% 4.01/0.98  --splitting_cvd_svl                     false
% 4.01/0.98  --splitting_nvd                         32
% 4.01/0.98  --sub_typing                            true
% 4.01/0.98  --prep_gs_sim                           true
% 4.01/0.98  --prep_unflatten                        true
% 4.01/0.98  --prep_res_sim                          true
% 4.01/0.98  --prep_upred                            true
% 4.01/0.98  --prep_sem_filter                       exhaustive
% 4.01/0.98  --prep_sem_filter_out                   false
% 4.01/0.98  --pred_elim                             true
% 4.01/0.98  --res_sim_input                         true
% 4.01/0.98  --eq_ax_congr_red                       true
% 4.01/0.98  --pure_diseq_elim                       true
% 4.01/0.98  --brand_transform                       false
% 4.01/0.98  --non_eq_to_eq                          false
% 4.01/0.98  --prep_def_merge                        true
% 4.01/0.98  --prep_def_merge_prop_impl              false
% 4.01/0.98  --prep_def_merge_mbd                    true
% 4.01/0.98  --prep_def_merge_tr_red                 false
% 4.01/0.98  --prep_def_merge_tr_cl                  false
% 4.01/0.98  --smt_preprocessing                     true
% 4.01/0.98  --smt_ac_axioms                         fast
% 4.01/0.98  --preprocessed_out                      false
% 4.01/0.98  --preprocessed_stats                    false
% 4.01/0.98  
% 4.01/0.98  ------ Abstraction refinement Options
% 4.01/0.98  
% 4.01/0.98  --abstr_ref                             []
% 4.01/0.98  --abstr_ref_prep                        false
% 4.01/0.98  --abstr_ref_until_sat                   false
% 4.01/0.98  --abstr_ref_sig_restrict                funpre
% 4.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/0.98  --abstr_ref_under                       []
% 4.01/0.98  
% 4.01/0.98  ------ SAT Options
% 4.01/0.98  
% 4.01/0.98  --sat_mode                              false
% 4.01/0.98  --sat_fm_restart_options                ""
% 4.01/0.98  --sat_gr_def                            false
% 4.01/0.98  --sat_epr_types                         true
% 4.01/0.98  --sat_non_cyclic_types                  false
% 4.01/0.98  --sat_finite_models                     false
% 4.01/0.98  --sat_fm_lemmas                         false
% 4.01/0.98  --sat_fm_prep                           false
% 4.01/0.98  --sat_fm_uc_incr                        true
% 4.01/0.98  --sat_out_model                         small
% 4.01/0.98  --sat_out_clauses                       false
% 4.01/0.98  
% 4.01/0.98  ------ QBF Options
% 4.01/0.98  
% 4.01/0.98  --qbf_mode                              false
% 4.01/0.98  --qbf_elim_univ                         false
% 4.01/0.98  --qbf_dom_inst                          none
% 4.01/0.98  --qbf_dom_pre_inst                      false
% 4.01/0.98  --qbf_sk_in                             false
% 4.01/0.98  --qbf_pred_elim                         true
% 4.01/0.98  --qbf_split                             512
% 4.01/0.98  
% 4.01/0.98  ------ BMC1 Options
% 4.01/0.98  
% 4.01/0.98  --bmc1_incremental                      false
% 4.01/0.98  --bmc1_axioms                           reachable_all
% 4.01/0.98  --bmc1_min_bound                        0
% 4.01/0.98  --bmc1_max_bound                        -1
% 4.01/0.98  --bmc1_max_bound_default                -1
% 4.01/0.98  --bmc1_symbol_reachability              true
% 4.01/0.98  --bmc1_property_lemmas                  false
% 4.01/0.98  --bmc1_k_induction                      false
% 4.01/0.98  --bmc1_non_equiv_states                 false
% 4.01/0.98  --bmc1_deadlock                         false
% 4.01/0.98  --bmc1_ucm                              false
% 4.01/0.98  --bmc1_add_unsat_core                   none
% 4.01/0.98  --bmc1_unsat_core_children              false
% 4.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/0.98  --bmc1_out_stat                         full
% 4.01/0.98  --bmc1_ground_init                      false
% 4.01/0.98  --bmc1_pre_inst_next_state              false
% 4.01/0.98  --bmc1_pre_inst_state                   false
% 4.01/0.98  --bmc1_pre_inst_reach_state             false
% 4.01/0.98  --bmc1_out_unsat_core                   false
% 4.01/0.98  --bmc1_aig_witness_out                  false
% 4.01/0.98  --bmc1_verbose                          false
% 4.01/0.98  --bmc1_dump_clauses_tptp                false
% 4.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.01/0.98  --bmc1_dump_file                        -
% 4.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.01/0.98  --bmc1_ucm_extend_mode                  1
% 4.01/0.98  --bmc1_ucm_init_mode                    2
% 4.01/0.98  --bmc1_ucm_cone_mode                    none
% 4.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.01/0.98  --bmc1_ucm_relax_model                  4
% 4.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/0.98  --bmc1_ucm_layered_model                none
% 4.01/0.98  --bmc1_ucm_max_lemma_size               10
% 4.01/0.98  
% 4.01/0.98  ------ AIG Options
% 4.01/0.98  
% 4.01/0.98  --aig_mode                              false
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation Options
% 4.01/0.98  
% 4.01/0.98  --instantiation_flag                    true
% 4.01/0.98  --inst_sos_flag                         true
% 4.01/0.98  --inst_sos_phase                        true
% 4.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel_side                     num_symb
% 4.01/0.98  --inst_solver_per_active                1400
% 4.01/0.98  --inst_solver_calls_frac                1.
% 4.01/0.98  --inst_passive_queue_type               priority_queues
% 4.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/0.98  --inst_passive_queues_freq              [25;2]
% 4.01/0.98  --inst_dismatching                      true
% 4.01/0.98  --inst_eager_unprocessed_to_passive     true
% 4.01/0.98  --inst_prop_sim_given                   true
% 4.01/0.98  --inst_prop_sim_new                     false
% 4.01/0.98  --inst_subs_new                         false
% 4.01/0.98  --inst_eq_res_simp                      false
% 4.01/0.98  --inst_subs_given                       false
% 4.01/0.98  --inst_orphan_elimination               true
% 4.01/0.98  --inst_learning_loop_flag               true
% 4.01/0.98  --inst_learning_start                   3000
% 4.01/0.98  --inst_learning_factor                  2
% 4.01/0.98  --inst_start_prop_sim_after_learn       3
% 4.01/0.98  --inst_sel_renew                        solver
% 4.01/0.98  --inst_lit_activity_flag                true
% 4.01/0.98  --inst_restr_to_given                   false
% 4.01/0.98  --inst_activity_threshold               500
% 4.01/0.98  --inst_out_proof                        true
% 4.01/0.98  
% 4.01/0.98  ------ Resolution Options
% 4.01/0.98  
% 4.01/0.98  --resolution_flag                       true
% 4.01/0.98  --res_lit_sel                           adaptive
% 4.01/0.98  --res_lit_sel_side                      none
% 4.01/0.98  --res_ordering                          kbo
% 4.01/0.98  --res_to_prop_solver                    active
% 4.01/0.98  --res_prop_simpl_new                    false
% 4.01/0.98  --res_prop_simpl_given                  true
% 4.01/0.98  --res_passive_queue_type                priority_queues
% 4.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/0.98  --res_passive_queues_freq               [15;5]
% 4.01/0.98  --res_forward_subs                      full
% 4.01/0.98  --res_backward_subs                     full
% 4.01/0.98  --res_forward_subs_resolution           true
% 4.01/0.98  --res_backward_subs_resolution          true
% 4.01/0.98  --res_orphan_elimination                true
% 4.01/0.98  --res_time_limit                        2.
% 4.01/0.98  --res_out_proof                         true
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Options
% 4.01/0.98  
% 4.01/0.98  --superposition_flag                    true
% 4.01/0.98  --sup_passive_queue_type                priority_queues
% 4.01/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.01/0.98  --demod_completeness_check              fast
% 4.01/0.98  --demod_use_ground                      true
% 4.01/0.98  --sup_to_prop_solver                    passive
% 4.01/0.98  --sup_prop_simpl_new                    true
% 4.01/0.98  --sup_prop_simpl_given                  true
% 4.01/0.98  --sup_fun_splitting                     true
% 4.01/0.98  --sup_smt_interval                      50000
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Simplification Setup
% 4.01/0.98  
% 4.01/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.01/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.01/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.01/0.98  --sup_immed_triv                        [TrivRules]
% 4.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_bw_main                     []
% 4.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_input_bw                          []
% 4.01/0.98  
% 4.01/0.98  ------ Combination Options
% 4.01/0.98  
% 4.01/0.98  --comb_res_mult                         3
% 4.01/0.98  --comb_sup_mult                         2
% 4.01/0.98  --comb_inst_mult                        10
% 4.01/0.98  
% 4.01/0.98  ------ Debug Options
% 4.01/0.98  
% 4.01/0.98  --dbg_backtrace                         false
% 4.01/0.98  --dbg_dump_prop_clauses                 false
% 4.01/0.98  --dbg_dump_prop_clauses_file            -
% 4.01/0.98  --dbg_out_stat                          false
% 4.01/0.98  ------ Parsing...
% 4.01/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/0.98  ------ Proving...
% 4.01/0.98  ------ Problem Properties 
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  clauses                                 15
% 4.01/0.98  conjectures                             2
% 4.01/0.98  EPR                                     2
% 4.01/0.98  Horn                                    12
% 4.01/0.98  unary                                   4
% 4.01/0.98  binary                                  2
% 4.01/0.98  lits                                    53
% 4.01/0.98  lits eq                                 6
% 4.01/0.98  fd_pure                                 0
% 4.01/0.98  fd_pseudo                               0
% 4.01/0.98  fd_cond                                 0
% 4.01/0.98  fd_pseudo_cond                          3
% 4.01/0.98  AC symbols                              0
% 4.01/0.98  
% 4.01/0.98  ------ Schedule dynamic 5 is on 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  Current options:
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options
% 4.01/0.98  
% 4.01/0.98  --out_options                           all
% 4.01/0.98  --tptp_safe_out                         true
% 4.01/0.98  --problem_path                          ""
% 4.01/0.98  --include_path                          ""
% 4.01/0.98  --clausifier                            res/vclausify_rel
% 4.01/0.98  --clausifier_options                    ""
% 4.01/0.98  --stdin                                 false
% 4.01/0.98  --stats_out                             all
% 4.01/0.98  
% 4.01/0.98  ------ General Options
% 4.01/0.98  
% 4.01/0.98  --fof                                   false
% 4.01/0.98  --time_out_real                         305.
% 4.01/0.98  --time_out_virtual                      -1.
% 4.01/0.98  --symbol_type_check                     false
% 4.01/0.98  --clausify_out                          false
% 4.01/0.98  --sig_cnt_out                           false
% 4.01/0.98  --trig_cnt_out                          false
% 4.01/0.98  --trig_cnt_out_tolerance                1.
% 4.01/0.98  --trig_cnt_out_sk_spl                   false
% 4.01/0.98  --abstr_cl_out                          false
% 4.01/0.98  
% 4.01/0.98  ------ Global Options
% 4.01/0.98  
% 4.01/0.98  --schedule                              default
% 4.01/0.98  --add_important_lit                     false
% 4.01/0.98  --prop_solver_per_cl                    1000
% 4.01/0.98  --min_unsat_core                        false
% 4.01/0.98  --soft_assumptions                      false
% 4.01/0.98  --soft_lemma_size                       3
% 4.01/0.98  --prop_impl_unit_size                   0
% 4.01/0.98  --prop_impl_unit                        []
% 4.01/0.98  --share_sel_clauses                     true
% 4.01/0.98  --reset_solvers                         false
% 4.01/0.98  --bc_imp_inh                            [conj_cone]
% 4.01/0.98  --conj_cone_tolerance                   3.
% 4.01/0.98  --extra_neg_conj                        none
% 4.01/0.98  --large_theory_mode                     true
% 4.01/0.98  --prolific_symb_bound                   200
% 4.01/0.98  --lt_threshold                          2000
% 4.01/0.98  --clause_weak_htbl                      true
% 4.01/0.98  --gc_record_bc_elim                     false
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing Options
% 4.01/0.98  
% 4.01/0.98  --preprocessing_flag                    true
% 4.01/0.98  --time_out_prep_mult                    0.1
% 4.01/0.98  --splitting_mode                        input
% 4.01/0.98  --splitting_grd                         true
% 4.01/0.98  --splitting_cvd                         false
% 4.01/0.98  --splitting_cvd_svl                     false
% 4.01/0.98  --splitting_nvd                         32
% 4.01/0.98  --sub_typing                            true
% 4.01/0.98  --prep_gs_sim                           true
% 4.01/0.98  --prep_unflatten                        true
% 4.01/0.98  --prep_res_sim                          true
% 4.01/0.98  --prep_upred                            true
% 4.01/0.98  --prep_sem_filter                       exhaustive
% 4.01/0.98  --prep_sem_filter_out                   false
% 4.01/0.98  --pred_elim                             true
% 4.01/0.98  --res_sim_input                         true
% 4.01/0.98  --eq_ax_congr_red                       true
% 4.01/0.98  --pure_diseq_elim                       true
% 4.01/0.98  --brand_transform                       false
% 4.01/0.98  --non_eq_to_eq                          false
% 4.01/0.98  --prep_def_merge                        true
% 4.01/0.98  --prep_def_merge_prop_impl              false
% 4.01/0.98  --prep_def_merge_mbd                    true
% 4.01/0.98  --prep_def_merge_tr_red                 false
% 4.01/0.98  --prep_def_merge_tr_cl                  false
% 4.01/0.98  --smt_preprocessing                     true
% 4.01/0.98  --smt_ac_axioms                         fast
% 4.01/0.98  --preprocessed_out                      false
% 4.01/0.98  --preprocessed_stats                    false
% 4.01/0.98  
% 4.01/0.98  ------ Abstraction refinement Options
% 4.01/0.98  
% 4.01/0.98  --abstr_ref                             []
% 4.01/0.98  --abstr_ref_prep                        false
% 4.01/0.98  --abstr_ref_until_sat                   false
% 4.01/0.98  --abstr_ref_sig_restrict                funpre
% 4.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/0.98  --abstr_ref_under                       []
% 4.01/0.98  
% 4.01/0.98  ------ SAT Options
% 4.01/0.98  
% 4.01/0.98  --sat_mode                              false
% 4.01/0.98  --sat_fm_restart_options                ""
% 4.01/0.98  --sat_gr_def                            false
% 4.01/0.98  --sat_epr_types                         true
% 4.01/0.98  --sat_non_cyclic_types                  false
% 4.01/0.98  --sat_finite_models                     false
% 4.01/0.98  --sat_fm_lemmas                         false
% 4.01/0.98  --sat_fm_prep                           false
% 4.01/0.98  --sat_fm_uc_incr                        true
% 4.01/0.98  --sat_out_model                         small
% 4.01/0.98  --sat_out_clauses                       false
% 4.01/0.98  
% 4.01/0.98  ------ QBF Options
% 4.01/0.98  
% 4.01/0.98  --qbf_mode                              false
% 4.01/0.98  --qbf_elim_univ                         false
% 4.01/0.98  --qbf_dom_inst                          none
% 4.01/0.98  --qbf_dom_pre_inst                      false
% 4.01/0.98  --qbf_sk_in                             false
% 4.01/0.98  --qbf_pred_elim                         true
% 4.01/0.98  --qbf_split                             512
% 4.01/0.98  
% 4.01/0.98  ------ BMC1 Options
% 4.01/0.98  
% 4.01/0.98  --bmc1_incremental                      false
% 4.01/0.98  --bmc1_axioms                           reachable_all
% 4.01/0.98  --bmc1_min_bound                        0
% 4.01/0.98  --bmc1_max_bound                        -1
% 4.01/0.98  --bmc1_max_bound_default                -1
% 4.01/0.98  --bmc1_symbol_reachability              true
% 4.01/0.98  --bmc1_property_lemmas                  false
% 4.01/0.98  --bmc1_k_induction                      false
% 4.01/0.98  --bmc1_non_equiv_states                 false
% 4.01/0.98  --bmc1_deadlock                         false
% 4.01/0.98  --bmc1_ucm                              false
% 4.01/0.98  --bmc1_add_unsat_core                   none
% 4.01/0.98  --bmc1_unsat_core_children              false
% 4.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/0.98  --bmc1_out_stat                         full
% 4.01/0.98  --bmc1_ground_init                      false
% 4.01/0.98  --bmc1_pre_inst_next_state              false
% 4.01/0.98  --bmc1_pre_inst_state                   false
% 4.01/0.98  --bmc1_pre_inst_reach_state             false
% 4.01/0.98  --bmc1_out_unsat_core                   false
% 4.01/0.98  --bmc1_aig_witness_out                  false
% 4.01/0.98  --bmc1_verbose                          false
% 4.01/0.98  --bmc1_dump_clauses_tptp                false
% 4.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.01/0.98  --bmc1_dump_file                        -
% 4.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.01/0.98  --bmc1_ucm_extend_mode                  1
% 4.01/0.98  --bmc1_ucm_init_mode                    2
% 4.01/0.98  --bmc1_ucm_cone_mode                    none
% 4.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.01/0.98  --bmc1_ucm_relax_model                  4
% 4.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/0.98  --bmc1_ucm_layered_model                none
% 4.01/0.98  --bmc1_ucm_max_lemma_size               10
% 4.01/0.98  
% 4.01/0.98  ------ AIG Options
% 4.01/0.98  
% 4.01/0.98  --aig_mode                              false
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation Options
% 4.01/0.98  
% 4.01/0.98  --instantiation_flag                    true
% 4.01/0.98  --inst_sos_flag                         true
% 4.01/0.98  --inst_sos_phase                        true
% 4.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel_side                     none
% 4.01/0.98  --inst_solver_per_active                1400
% 4.01/0.98  --inst_solver_calls_frac                1.
% 4.01/0.98  --inst_passive_queue_type               priority_queues
% 4.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/0.98  --inst_passive_queues_freq              [25;2]
% 4.01/0.98  --inst_dismatching                      true
% 4.01/0.98  --inst_eager_unprocessed_to_passive     true
% 4.01/0.98  --inst_prop_sim_given                   true
% 4.01/0.98  --inst_prop_sim_new                     false
% 4.01/0.98  --inst_subs_new                         false
% 4.01/0.98  --inst_eq_res_simp                      false
% 4.01/0.98  --inst_subs_given                       false
% 4.01/0.98  --inst_orphan_elimination               true
% 4.01/0.98  --inst_learning_loop_flag               true
% 4.01/0.98  --inst_learning_start                   3000
% 4.01/0.98  --inst_learning_factor                  2
% 4.01/0.98  --inst_start_prop_sim_after_learn       3
% 4.01/0.98  --inst_sel_renew                        solver
% 4.01/0.98  --inst_lit_activity_flag                true
% 4.01/0.98  --inst_restr_to_given                   false
% 4.01/0.98  --inst_activity_threshold               500
% 4.01/0.98  --inst_out_proof                        true
% 4.01/0.98  
% 4.01/0.98  ------ Resolution Options
% 4.01/0.98  
% 4.01/0.98  --resolution_flag                       false
% 4.01/0.98  --res_lit_sel                           adaptive
% 4.01/0.98  --res_lit_sel_side                      none
% 4.01/0.98  --res_ordering                          kbo
% 4.01/0.98  --res_to_prop_solver                    active
% 4.01/0.98  --res_prop_simpl_new                    false
% 4.01/0.98  --res_prop_simpl_given                  true
% 4.01/0.98  --res_passive_queue_type                priority_queues
% 4.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/0.98  --res_passive_queues_freq               [15;5]
% 4.01/0.98  --res_forward_subs                      full
% 4.01/0.98  --res_backward_subs                     full
% 4.01/0.98  --res_forward_subs_resolution           true
% 4.01/0.98  --res_backward_subs_resolution          true
% 4.01/0.98  --res_orphan_elimination                true
% 4.01/0.98  --res_time_limit                        2.
% 4.01/0.98  --res_out_proof                         true
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Options
% 4.01/0.98  
% 4.01/0.98  --superposition_flag                    true
% 4.01/0.98  --sup_passive_queue_type                priority_queues
% 4.01/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.01/0.98  --demod_completeness_check              fast
% 4.01/0.98  --demod_use_ground                      true
% 4.01/0.98  --sup_to_prop_solver                    passive
% 4.01/0.98  --sup_prop_simpl_new                    true
% 4.01/0.98  --sup_prop_simpl_given                  true
% 4.01/0.98  --sup_fun_splitting                     true
% 4.01/0.98  --sup_smt_interval                      50000
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Simplification Setup
% 4.01/0.98  
% 4.01/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.01/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.01/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.01/0.98  --sup_immed_triv                        [TrivRules]
% 4.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_bw_main                     []
% 4.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_input_bw                          []
% 4.01/0.98  
% 4.01/0.98  ------ Combination Options
% 4.01/0.98  
% 4.01/0.98  --comb_res_mult                         3
% 4.01/0.98  --comb_sup_mult                         2
% 4.01/0.98  --comb_inst_mult                        10
% 4.01/0.98  
% 4.01/0.98  ------ Debug Options
% 4.01/0.98  
% 4.01/0.98  --dbg_backtrace                         false
% 4.01/0.98  --dbg_dump_prop_clauses                 false
% 4.01/0.98  --dbg_dump_prop_clauses_file            -
% 4.01/0.98  --dbg_out_stat                          false
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ Proving...
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS status Theorem for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  fof(f7,conjecture,(
% 4.01/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f8,negated_conjecture,(
% 4.01/0.98    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 4.01/0.98    inference(negated_conjecture,[],[f7])).
% 4.01/0.98  
% 4.01/0.98  fof(f12,plain,(
% 4.01/0.98    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f8])).
% 4.01/0.98  
% 4.01/0.98  fof(f23,plain,(
% 4.01/0.98    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)) & v1_relat_1(sK6))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f24,plain,(
% 4.01/0.98    (k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)) & v1_relat_1(sK6)),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f12,f23])).
% 4.01/0.98  
% 4.01/0.98  fof(f38,plain,(
% 4.01/0.98    v1_relat_1(sK6)),
% 4.01/0.98    inference(cnf_transformation,[],[f24])).
% 4.01/0.98  
% 4.01/0.98  fof(f1,axiom,(
% 4.01/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f25,plain,(
% 4.01/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f1])).
% 4.01/0.98  
% 4.01/0.98  fof(f5,axiom,(
% 4.01/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f10,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f5])).
% 4.01/0.98  
% 4.01/0.98  fof(f17,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(nnf_transformation,[],[f10])).
% 4.01/0.98  
% 4.01/0.98  fof(f18,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(rectify,[],[f17])).
% 4.01/0.98  
% 4.01/0.98  fof(f21,plain,(
% 4.01/0.98    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f20,plain,(
% 4.01/0.98    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f19,plain,(
% 4.01/0.98    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f22,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).
% 4.01/0.98  
% 4.01/0.98  fof(f35,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f22])).
% 4.01/0.98  
% 4.01/0.98  fof(f4,axiom,(
% 4.01/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f9,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f4])).
% 4.01/0.98  
% 4.01/0.98  fof(f13,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(nnf_transformation,[],[f9])).
% 4.01/0.98  
% 4.01/0.98  fof(f14,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(rectify,[],[f13])).
% 4.01/0.98  
% 4.01/0.98  fof(f15,plain,(
% 4.01/0.98    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f16,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 4.01/0.98  
% 4.01/0.98  fof(f28,plain,(
% 4.01/0.98    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f16])).
% 4.01/0.98  
% 4.01/0.98  fof(f3,axiom,(
% 4.01/0.98    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f27,plain,(
% 4.01/0.98    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 4.01/0.98    inference(cnf_transformation,[],[f3])).
% 4.01/0.98  
% 4.01/0.98  fof(f2,axiom,(
% 4.01/0.98    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f26,plain,(
% 4.01/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.01/0.98    inference(cnf_transformation,[],[f2])).
% 4.01/0.98  
% 4.01/0.98  fof(f6,axiom,(
% 4.01/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f11,plain,(
% 4.01/0.98    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f6])).
% 4.01/0.98  
% 4.01/0.98  fof(f37,plain,(
% 4.01/0.98    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f11])).
% 4.01/0.98  
% 4.01/0.98  fof(f34,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f22])).
% 4.01/0.98  
% 4.01/0.98  fof(f32,plain,(
% 4.01/0.98    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f22])).
% 4.01/0.98  
% 4.01/0.98  fof(f41,plain,(
% 4.01/0.98    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.01/0.98    inference(equality_resolution,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  fof(f31,plain,(
% 4.01/0.98    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f22])).
% 4.01/0.98  
% 4.01/0.98  fof(f42,plain,(
% 4.01/0.98    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.01/0.98    inference(equality_resolution,[],[f31])).
% 4.01/0.98  
% 4.01/0.98  fof(f39,plain,(
% 4.01/0.98    k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)),
% 4.01/0.98    inference(cnf_transformation,[],[f24])).
% 4.01/0.98  
% 4.01/0.98  cnf(c_14,negated_conjecture,
% 4.01/0.98      ( v1_relat_1(sK6) ),
% 4.01/0.98      inference(cnf_transformation,[],[f38]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_208,negated_conjecture,
% 4.01/0.98      ( v1_relat_1(sK6) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_483,plain,
% 4.01/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_0,plain,
% 4.01/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f25]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_222,plain,
% 4.01/0.98      ( r1_tarski(k1_xboole_0,X0_44) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_471,plain,
% 4.01/0.98      ( r1_tarski(k1_xboole_0,X0_44) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
% 4.01/0.98      | ~ v1_relat_1(X0)
% 4.01/0.98      | ~ v1_relat_1(X2)
% 4.01/0.98      | ~ v1_relat_1(X1)
% 4.01/0.98      | k5_relat_1(X0,X1) = X2 ),
% 4.01/0.98      inference(cnf_transformation,[],[f35]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_215,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(sK4(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X1_44)
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X2_44)
% 4.01/0.98      | ~ v1_relat_1(X0_44)
% 4.01/0.98      | ~ v1_relat_1(X2_44)
% 4.01/0.98      | ~ v1_relat_1(X1_44)
% 4.01/0.98      | k5_relat_1(X0_44,X1_44) = X2_44 ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_477,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = X2_44
% 4.01/0.98      | r2_hidden(k4_tarski(sK4(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X1_44) = iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X2_44) = iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5,plain,
% 4.01/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 4.01/0.98      | r2_hidden(k4_tarski(X0,X1),X3)
% 4.01/0.98      | ~ r1_tarski(X2,X3)
% 4.01/0.98      | ~ v1_relat_1(X2) ),
% 4.01/0.98      inference(cnf_transformation,[],[f28]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_217,plain,
% 4.01/0.98      ( ~ r2_hidden(k4_tarski(X0_47,X1_47),X0_44)
% 4.01/0.98      | r2_hidden(k4_tarski(X0_47,X1_47),X1_44)
% 4.01/0.98      | ~ r1_tarski(X0_44,X1_44)
% 4.01/0.98      | ~ v1_relat_1(X0_44) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_475,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),X0_44) != iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(X0_47,X1_47),X1_44) = iProver_top
% 4.01/0.98      | r1_tarski(X0_44,X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1656,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = X2_44
% 4.01/0.98      | r2_hidden(k4_tarski(sK4(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X1_44) = iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X3_44) = iProver_top
% 4.01/0.98      | r1_tarski(X2_44,X3_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_477,c_475]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2,plain,
% 4.01/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f27]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_220,plain,
% 4.01/0.98      ( ~ r2_hidden(X0_46,k2_zfmisc_1(X0_46,X0_48)) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_472,plain,
% 4.01/0.98      ( r2_hidden(X0_46,k2_zfmisc_1(X0_46,X0_48)) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7286,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = X2_44
% 4.01/0.98      | r2_hidden(k4_tarski(sK4(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X1_44) = iProver_top
% 4.01/0.98      | r1_tarski(X2_44,k2_zfmisc_1(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X0_48)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1656,c_472]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7368,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = k1_xboole_0
% 4.01/0.98      | r2_hidden(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X1_44) = iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_471,c_7286]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1,plain,
% 4.01/0.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 4.01/0.98      inference(cnf_transformation,[],[f26]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_221,plain,
% 4.01/0.98      ( k4_xboole_0(X0_44,k2_xboole_0(X0_44,X0_49)) = k1_xboole_0 ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12,plain,
% 4.01/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k4_xboole_0(X0,X1)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f37]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_210,plain,
% 4.01/0.98      ( ~ v1_relat_1(X0_44) | v1_relat_1(k4_xboole_0(X0_44,X0_45)) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_482,plain,
% 4.01/0.98      ( v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k4_xboole_0(X0_44,X0_45)) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_629,plain,
% 4.01/0.98      ( v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_221,c_482]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_684,plain,
% 4.01/0.98      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_483,c_629]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7765,plain,
% 4.01/0.98      ( v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X1_44) = iProver_top
% 4.01/0.98      | k5_relat_1(X0_44,X1_44) = k1_xboole_0 ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_7368,c_684]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7766,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = k1_xboole_0
% 4.01/0.98      | r2_hidden(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X1_44) = iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_7765]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_7776,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = k1_xboole_0
% 4.01/0.98      | r2_hidden(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X2_44) = iProver_top
% 4.01/0.98      | r1_tarski(X1_44,X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_7766,c_475]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9033,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = k1_xboole_0
% 4.01/0.98      | r1_tarski(X1_44,k2_zfmisc_1(k4_tarski(sK4(X0_44,X1_44,k1_xboole_0),sK3(X0_44,X1_44,k1_xboole_0)),X0_48)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_7776,c_472]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9078,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,k1_xboole_0) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_471,c_9033]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9232,plain,
% 4.01/0.98      ( v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | k5_relat_1(X0_44,k1_xboole_0) = k1_xboole_0 ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_9078,c_684]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9233,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,k1_xboole_0) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_9232]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9236,plain,
% 4.01/0.98      ( k5_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_483,c_9233]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
% 4.01/0.98      | ~ v1_relat_1(X0)
% 4.01/0.98      | ~ v1_relat_1(X2)
% 4.01/0.98      | ~ v1_relat_1(X1)
% 4.01/0.98      | k5_relat_1(X0,X1) = X2 ),
% 4.01/0.98      inference(cnf_transformation,[],[f34]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_214,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK4(X0_44,X1_44,X2_44)),X0_44)
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X2_44)
% 4.01/0.98      | ~ v1_relat_1(X0_44)
% 4.01/0.98      | ~ v1_relat_1(X2_44)
% 4.01/0.98      | ~ v1_relat_1(X1_44)
% 4.01/0.98      | k5_relat_1(X0_44,X1_44) = X2_44 ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_478,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = X2_44
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK4(X0_44,X1_44,X2_44)),X0_44) = iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0_44,X1_44,X2_44),sK3(X0_44,X1_44,X2_44)),X2_44) = iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10,plain,
% 4.01/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 4.01/0.98      | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
% 4.01/0.98      | ~ v1_relat_1(X2)
% 4.01/0.98      | ~ v1_relat_1(X3)
% 4.01/0.98      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_212,plain,
% 4.01/0.98      ( ~ r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44))
% 4.01/0.98      | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_47,X1_47),X1_47),X1_44)
% 4.01/0.98      | ~ v1_relat_1(X0_44)
% 4.01/0.98      | ~ v1_relat_1(X1_44)
% 4.01/0.98      | ~ v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_480,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_47,X1_47),X1_47),X1_44) = iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_840,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(sK5(X0_44,X1_44,X0_47,X1_47),X1_47),X2_44) = iProver_top
% 4.01/0.98      | r1_tarski(X1_44,X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_480,c_475]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1113,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
% 4.01/0.98      | r1_tarski(X1_44,k2_zfmisc_1(k4_tarski(sK5(X0_44,X1_44,X0_47,X1_47),X1_47),X0_48)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_840,c_472]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1195,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_471,c_1113]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1200,plain,
% 4.01/0.98      ( v1_relat_1(k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,k1_xboole_0)) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_1195,c_684]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1201,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,k1_xboole_0)) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_1200]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1693,plain,
% 4.01/0.98      ( k5_relat_1(X0_44,X1_44) = k5_relat_1(X2_44,k1_xboole_0)
% 4.01/0.98      | r2_hidden(k4_tarski(sK2(X0_44,X1_44,k5_relat_1(X2_44,k1_xboole_0)),sK4(X0_44,X1_44,k5_relat_1(X2_44,k1_xboole_0))),X0_44) = iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X2_44,k1_xboole_0)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_478,c_1201]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4692,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(X0_44,k1_xboole_0),X1_44) = k5_relat_1(X2_44,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X2_44,k1_xboole_0)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1693,c_1201]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9258,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(sK6,k1_xboole_0),X0_44) = k5_relat_1(X1_44,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(sK6) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_9236,c_4692]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9307,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,X0_44) = k5_relat_1(X1_44,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(sK6) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_9258,c_9236]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9237,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_684,c_9233]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9588,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X0_44) = k5_relat_1(X1_44,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_9237,c_4692]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9664,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,X0_44) = k5_relat_1(X1_44,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_9588,c_9237]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10136,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,X0_44) = k5_relat_1(X1_44,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X1_44,k1_xboole_0)) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_9307,c_684,c_9664]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10140,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,X0_44) = k5_relat_1(sK6,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(sK6) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_9236,c_10136]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10143,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,X0_44) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(sK6) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_10140,c_9236]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_11,plain,
% 4.01/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 4.01/0.98      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
% 4.01/0.98      | ~ v1_relat_1(X2)
% 4.01/0.98      | ~ v1_relat_1(X3)
% 4.01/0.98      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_211,plain,
% 4.01/0.98      ( ~ r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44))
% 4.01/0.98      | r2_hidden(k4_tarski(X0_47,sK5(X0_44,X1_44,X0_47,X1_47)),X0_44)
% 4.01/0.98      | ~ v1_relat_1(X0_44)
% 4.01/0.98      | ~ v1_relat_1(X1_44)
% 4.01/0.98      | ~ v1_relat_1(k5_relat_1(X0_44,X1_44)) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_481,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(X0_47,sK5(X0_44,X1_44,X0_47,X1_47)),X0_44) = iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_994,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(X0_47,sK5(X0_44,X1_44,X0_47,X1_47)),X2_44) = iProver_top
% 4.01/0.98      | r1_tarski(X0_44,X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_481,c_475]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2078,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(X0_44,X1_44)) != iProver_top
% 4.01/0.98      | r1_tarski(X0_44,k2_zfmisc_1(k4_tarski(X0_47,sK5(X0_44,X1_44,X0_47,X1_47)),X0_48)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X0_44,X1_44)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_994,c_472]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2206,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_471,c_2078]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2212,plain,
% 4.01/0.98      ( v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(k1_xboole_0,X0_44)) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_2206,c_684]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2213,plain,
% 4.01/0.98      ( r2_hidden(k4_tarski(X0_47,X1_47),k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_2212]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_4695,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k5_relat_1(X2_44,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X2_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(X2_44,k1_xboole_0)) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1693,c_2213]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9277,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k5_relat_1(sK6,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
% 4.01/0.98      | v1_relat_1(sK6) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_9236,c_4695]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9291,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
% 4.01/0.98      | v1_relat_1(sK6) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_9277,c_9236]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9607,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k5_relat_1(k1_xboole_0,k1_xboole_0)
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_9237,c_4695]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9661,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_9607,c_9237]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9853,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(k1_xboole_0,X0_44),X1_44) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(X1_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k5_relat_1(k1_xboole_0,X0_44)) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_9291,c_684,c_9661]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9857,plain,
% 4.01/0.98      ( k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X0_44) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_9237,c_9853]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9858,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,X0_44) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top
% 4.01/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_9857,c_9237]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10146,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,X0_44) = k1_xboole_0
% 4.01/0.98      | v1_relat_1(X0_44) != iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_10143,c_684,c_9858]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10150,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,sK6) = k1_xboole_0 ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_483,c_10146]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_13,negated_conjecture,
% 4.01/0.98      ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
% 4.01/0.98      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
% 4.01/0.98      inference(cnf_transformation,[],[f39]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_209,negated_conjecture,
% 4.01/0.98      ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
% 4.01/0.98      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9242,plain,
% 4.01/0.98      ( k5_relat_1(k1_xboole_0,sK6) != k1_xboole_0
% 4.01/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 4.01/0.98      inference(demodulation,[status(thm)],[c_9236,c_209]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_224,plain,( X0_44 = X0_44 ),theory(equality) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_242,plain,
% 4.01/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_224]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(contradiction,plain,
% 4.01/0.98      ( $false ),
% 4.01/0.98      inference(minisat,[status(thm)],[c_10150,c_9242,c_242]) ).
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  ------                               Statistics
% 4.01/0.98  
% 4.01/0.98  ------ General
% 4.01/0.98  
% 4.01/0.98  abstr_ref_over_cycles:                  0
% 4.01/0.98  abstr_ref_under_cycles:                 0
% 4.01/0.98  gc_basic_clause_elim:                   0
% 4.01/0.98  forced_gc_time:                         0
% 4.01/0.98  parsing_time:                           0.009
% 4.01/0.98  unif_index_cands_time:                  0.
% 4.01/0.98  unif_index_add_time:                    0.
% 4.01/0.98  orderings_time:                         0.
% 4.01/0.98  out_proof_time:                         0.009
% 4.01/0.98  total_time:                             0.363
% 4.01/0.98  num_of_symbols:                         53
% 4.01/0.98  num_of_terms:                           11233
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing
% 4.01/0.98  
% 4.01/0.98  num_of_splits:                          0
% 4.01/0.98  num_of_split_atoms:                     0
% 4.01/0.98  num_of_reused_defs:                     0
% 4.01/0.98  num_eq_ax_congr_red:                    46
% 4.01/0.98  num_of_sem_filtered_clauses:            1
% 4.01/0.98  num_of_subtypes:                        6
% 4.01/0.98  monotx_restored_types:                  0
% 4.01/0.98  sat_num_of_epr_types:                   0
% 4.01/0.98  sat_num_of_non_cyclic_types:            0
% 4.01/0.98  sat_guarded_non_collapsed_types:        1
% 4.01/0.98  num_pure_diseq_elim:                    0
% 4.01/0.98  simp_replaced_by:                       0
% 4.01/0.98  res_preprocessed:                       68
% 4.01/0.98  prep_upred:                             0
% 4.01/0.98  prep_unflattend:                        6
% 4.01/0.98  smt_new_axioms:                         0
% 4.01/0.98  pred_elim_cands:                        3
% 4.01/0.98  pred_elim:                              0
% 4.01/0.98  pred_elim_cl:                           0
% 4.01/0.98  pred_elim_cycles:                       1
% 4.01/0.98  merged_defs:                            0
% 4.01/0.98  merged_defs_ncl:                        0
% 4.01/0.98  bin_hyper_res:                          0
% 4.01/0.98  prep_cycles:                            3
% 4.01/0.98  pred_elim_time:                         0.001
% 4.01/0.98  splitting_time:                         0.
% 4.01/0.98  sem_filter_time:                        0.
% 4.01/0.98  monotx_time:                            0.
% 4.01/0.98  subtype_inf_time:                       0.
% 4.01/0.98  
% 4.01/0.98  ------ Problem properties
% 4.01/0.98  
% 4.01/0.98  clauses:                                15
% 4.01/0.98  conjectures:                            2
% 4.01/0.98  epr:                                    2
% 4.01/0.98  horn:                                   12
% 4.01/0.98  ground:                                 2
% 4.01/0.98  unary:                                  4
% 4.01/0.98  binary:                                 2
% 4.01/0.98  lits:                                   53
% 4.01/0.98  lits_eq:                                6
% 4.01/0.98  fd_pure:                                0
% 4.01/0.98  fd_pseudo:                              0
% 4.01/0.98  fd_cond:                                0
% 4.01/0.98  fd_pseudo_cond:                         3
% 4.01/0.98  ac_symbols:                             0
% 4.01/0.98  
% 4.01/0.98  ------ Propositional Solver
% 4.01/0.98  
% 4.01/0.98  prop_solver_calls:                      29
% 4.01/0.98  prop_fast_solver_calls:                 1073
% 4.01/0.98  smt_solver_calls:                       0
% 4.01/0.98  smt_fast_solver_calls:                  0
% 4.01/0.98  prop_num_of_clauses:                    3083
% 4.01/0.98  prop_preprocess_simplified:             5739
% 4.01/0.98  prop_fo_subsumed:                       19
% 4.01/0.98  prop_solver_time:                       0.
% 4.01/0.98  smt_solver_time:                        0.
% 4.01/0.98  smt_fast_solver_time:                   0.
% 4.01/0.98  prop_fast_solver_time:                  0.
% 4.01/0.98  prop_unsat_core_time:                   0.
% 4.01/0.98  
% 4.01/0.98  ------ QBF
% 4.01/0.98  
% 4.01/0.98  qbf_q_res:                              0
% 4.01/0.98  qbf_num_tautologies:                    0
% 4.01/0.98  qbf_prep_cycles:                        0
% 4.01/0.98  
% 4.01/0.98  ------ BMC1
% 4.01/0.98  
% 4.01/0.98  bmc1_current_bound:                     -1
% 4.01/0.98  bmc1_last_solved_bound:                 -1
% 4.01/0.98  bmc1_unsat_core_size:                   -1
% 4.01/0.98  bmc1_unsat_core_parents_size:           -1
% 4.01/0.98  bmc1_merge_next_fun:                    0
% 4.01/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation
% 4.01/0.98  
% 4.01/0.98  inst_num_of_clauses:                    677
% 4.01/0.98  inst_num_in_passive:                    115
% 4.01/0.98  inst_num_in_active:                     417
% 4.01/0.98  inst_num_in_unprocessed:                145
% 4.01/0.98  inst_num_of_loops:                      550
% 4.01/0.98  inst_num_of_learning_restarts:          0
% 4.01/0.98  inst_num_moves_active_passive:          127
% 4.01/0.98  inst_lit_activity:                      0
% 4.01/0.98  inst_lit_activity_moves:                0
% 4.01/0.98  inst_num_tautologies:                   0
% 4.01/0.98  inst_num_prop_implied:                  0
% 4.01/0.98  inst_num_existing_simplified:           0
% 4.01/0.98  inst_num_eq_res_simplified:             0
% 4.01/0.98  inst_num_child_elim:                    0
% 4.01/0.98  inst_num_of_dismatching_blockings:      1840
% 4.01/0.98  inst_num_of_non_proper_insts:           2251
% 4.01/0.98  inst_num_of_duplicates:                 0
% 4.01/0.98  inst_inst_num_from_inst_to_res:         0
% 4.01/0.98  inst_dismatching_checking_time:         0.
% 4.01/0.98  
% 4.01/0.98  ------ Resolution
% 4.01/0.98  
% 4.01/0.98  res_num_of_clauses:                     0
% 4.01/0.98  res_num_in_passive:                     0
% 4.01/0.98  res_num_in_active:                      0
% 4.01/0.98  res_num_of_loops:                       71
% 4.01/0.98  res_forward_subset_subsumed:            221
% 4.01/0.98  res_backward_subset_subsumed:           0
% 4.01/0.98  res_forward_subsumed:                   0
% 4.01/0.98  res_backward_subsumed:                  0
% 4.01/0.98  res_forward_subsumption_resolution:     0
% 4.01/0.98  res_backward_subsumption_resolution:    0
% 4.01/0.98  res_clause_to_clause_subsumption:       2469
% 4.01/0.98  res_orphan_elimination:                 0
% 4.01/0.98  res_tautology_del:                      278
% 4.01/0.98  res_num_eq_res_simplified:              0
% 4.01/0.98  res_num_sel_changes:                    0
% 4.01/0.98  res_moves_from_active_to_pass:          0
% 4.01/0.98  
% 4.01/0.98  ------ Superposition
% 4.01/0.98  
% 4.01/0.98  sup_time_total:                         0.
% 4.01/0.98  sup_time_generating:                    0.
% 4.01/0.98  sup_time_sim_full:                      0.
% 4.01/0.98  sup_time_sim_immed:                     0.
% 4.01/0.98  
% 4.01/0.98  sup_num_of_clauses:                     470
% 4.01/0.98  sup_num_in_active:                      101
% 4.01/0.98  sup_num_in_passive:                     369
% 4.01/0.98  sup_num_of_loops:                       109
% 4.01/0.98  sup_fw_superposition:                   375
% 4.01/0.98  sup_bw_superposition:                   359
% 4.01/0.98  sup_immediate_simplified:               193
% 4.01/0.98  sup_given_eliminated:                   2
% 4.01/0.98  comparisons_done:                       0
% 4.01/0.98  comparisons_avoided:                    0
% 4.01/0.98  
% 4.01/0.98  ------ Simplifications
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  sim_fw_subset_subsumed:                 24
% 4.01/0.98  sim_bw_subset_subsumed:                 7
% 4.01/0.98  sim_fw_subsumed:                        140
% 4.01/0.98  sim_bw_subsumed:                        11
% 4.01/0.98  sim_fw_subsumption_res:                 0
% 4.01/0.98  sim_bw_subsumption_res:                 0
% 4.01/0.98  sim_tautology_del:                      2
% 4.01/0.98  sim_eq_tautology_del:                   0
% 4.01/0.98  sim_eq_res_simp:                        1
% 4.01/0.98  sim_fw_demodulated:                     0
% 4.01/0.98  sim_bw_demodulated:                     1
% 4.01/0.98  sim_light_normalised:                   56
% 4.01/0.98  sim_joinable_taut:                      0
% 4.01/0.98  sim_joinable_simp:                      0
% 4.01/0.98  sim_ac_normalised:                      0
% 4.01/0.98  sim_smt_subsumption:                    0
% 4.01/0.98  
%------------------------------------------------------------------------------

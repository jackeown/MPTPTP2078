%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:45 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 447 expanded)
%              Number of clauses        :   56 ( 116 expanded)
%              Number of leaves         :   16 ( 120 expanded)
%              Depth                    :   21
%              Number of atoms          :  467 (2403 expanded)
%              Number of equality atoms :  140 ( 503 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22,f21,f20])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
             => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) != k1_funct_1(k5_relat_1(X2,X1),X0)
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) != k1_funct_1(k5_relat_1(X2,X1),X0)
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) != k1_funct_1(k5_relat_1(X2,X1),X0)
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_funct_1(X1,k1_funct_1(sK9,X0)) != k1_funct_1(k5_relat_1(sK9,X1),X0)
        & r2_hidden(X0,k1_relat_1(k5_relat_1(sK9,X1)))
        & v1_funct_1(sK9)
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k1_funct_1(X1,k1_funct_1(X2,X0)) != k1_funct_1(k5_relat_1(X2,X1),X0)
            & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,sK8),sK7) != k1_funct_1(sK8,k1_funct_1(X2,sK7))
          & r2_hidden(sK7,k1_relat_1(k5_relat_1(X2,sK8)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k1_funct_1(k5_relat_1(sK9,sK8),sK7) != k1_funct_1(sK8,k1_funct_1(sK9,sK7))
    & r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8)))
    & v1_funct_1(sK9)
    & v1_relat_1(sK9)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f16,f31,f30])).

fof(f55,plain,(
    k1_funct_1(k5_relat_1(sK9,sK8),sK7) != k1_funct_1(sK8,k1_funct_1(sK9,sK7)) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) ),
    inference(cnf_transformation,[],[f32])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f50,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f32])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_145,plain,
    ( ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_6])).

cnf(c_146,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_379,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_378,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1187,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_379,c_378])).

cnf(c_3443,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X1 = k1_funct_1(X2,X0) ),
    inference(resolution,[status(thm)],[c_146,c_1187])).

cnf(c_17,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK9,sK8),sK7) != k1_funct_1(sK8,k1_funct_1(sK9,sK7)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5640,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK9,sK7),k1_funct_1(k5_relat_1(sK9,sK8),sK7)),sK8)
    | ~ v1_relat_1(sK8)
    | ~ v1_funct_1(sK8) ),
    inference(resolution,[status(thm)],[c_3443,c_17])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v1_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_748,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_747,plain,
    ( r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_756,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_742,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_1173,plain,
    ( sK2(X0,X1) = k1_funct_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_742])).

cnf(c_1629,plain,
    ( sK2(k5_relat_1(sK9,sK8),sK7) = k1_funct_1(k5_relat_1(sK9,sK8),sK7)
    | v1_relat_1(k5_relat_1(sK9,sK8)) != iProver_top
    | v1_funct_1(k5_relat_1(sK9,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_747,c_1173])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1319,plain,
    ( v1_relat_1(k5_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1320,plain,
    ( v1_relat_1(k5_relat_1(sK9,sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_1673,plain,
    ( sK2(k5_relat_1(sK9,sK8),sK7) = k1_funct_1(k5_relat_1(sK9,sK8),sK7)
    | v1_funct_1(k5_relat_1(sK9,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_23,c_25,c_1320])).

cnf(c_1788,plain,
    ( sK2(k5_relat_1(sK9,sK8),sK7) = k1_funct_1(k5_relat_1(sK9,sK8),sK7)
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_1673])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1671,plain,
    ( ~ v1_relat_1(k5_relat_1(sK9,sK8))
    | ~ v1_funct_1(k5_relat_1(sK9,sK8))
    | sK2(k5_relat_1(sK9,sK8),sK7) = k1_funct_1(k5_relat_1(sK9,sK8),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1629])).

cnf(c_1717,plain,
    ( ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK9)
    | v1_funct_1(k5_relat_1(sK9,sK8))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1936,plain,
    ( sK2(k5_relat_1(sK9,sK8),sK7) = k1_funct_1(k5_relat_1(sK9,sK8),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1788,c_22,c_21,c_20,c_19,c_1319,c_1671,c_1717])).

cnf(c_1939,plain,
    ( r2_hidden(k4_tarski(sK7,k1_funct_1(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8)) = iProver_top
    | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_756])).

cnf(c_24,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_27,plain,
    ( r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1056,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | r2_hidden(k4_tarski(X0,k1_funct_1(k5_relat_1(X1,X2),X0)),k5_relat_1(X1,X2))
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(k5_relat_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1165,plain,
    ( r2_hidden(k4_tarski(sK7,k1_funct_1(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8))
    | ~ r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK9,sK8))
    | ~ v1_funct_1(k5_relat_1(sK9,sK8)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1166,plain,
    ( r2_hidden(k4_tarski(sK7,k1_funct_1(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8)) = iProver_top
    | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,sK8)) != iProver_top
    | v1_funct_1(k5_relat_1(sK9,sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_1718,plain,
    ( v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_funct_1(k5_relat_1(sK9,sK8)) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1717])).

cnf(c_1942,plain,
    ( r2_hidden(k4_tarski(sK7,k1_funct_1(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1939,c_23,c_24,c_25,c_26,c_27,c_1166,c_1320,c_1718])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_750,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_749,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_839,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_750,c_749])).

cnf(c_3168,plain,
    ( sK6(X0,X1,X2,X3) = k1_funct_1(X0,X2)
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_742])).

cnf(c_5258,plain,
    ( sK6(sK9,sK8,sK7,k1_funct_1(k5_relat_1(sK9,sK8),sK7)) = k1_funct_1(sK9,sK7)
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1942,c_3168])).

cnf(c_5432,plain,
    ( sK6(sK9,sK8,sK7,k1_funct_1(k5_relat_1(sK9,sK8),sK7)) = k1_funct_1(sK9,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5258,c_23,c_25,c_26])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK6(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_751,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_849,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_751,c_749])).

cnf(c_5435,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK9,sK7),k1_funct_1(k5_relat_1(sK9,sK8),sK7)),sK8) = iProver_top
    | r2_hidden(k4_tarski(sK7,k1_funct_1(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5432,c_849])).

cnf(c_5454,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK9,sK7),k1_funct_1(k5_relat_1(sK9,sK8),sK7)),sK8)
    | ~ r2_hidden(k4_tarski(sK7,k1_funct_1(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5435])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5640,c_5454,c_1717,c_1319,c_1165,c_18,c_19,c_20,c_21,c_22])).


%------------------------------------------------------------------------------

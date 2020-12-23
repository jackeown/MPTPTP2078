%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:14 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 591 expanded)
%              Number of clauses        :   68 ( 141 expanded)
%              Number of leaves         :   13 ( 151 expanded)
%              Depth                    :   24
%              Number of atoms          :  513 (3592 expanded)
%              Number of equality atoms :  220 (1564 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK5(X0,X1)) != sK5(X0,X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK5(X0,X1)) != sK5(X0,X1)
            & r2_hidden(sK5(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k1_relat_1(X1) = k2_relat_1(X0) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k1_relat_1(X1) = k2_relat_1(X0) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k6_relat_1(k1_relat_1(sK7)) != sK7
        & k5_relat_1(X0,sK7) = X0
        & k1_relat_1(sK7) = k2_relat_1(X0)
        & v1_funct_1(sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X1)) != X1
            & k5_relat_1(X0,X1) = X0
            & k1_relat_1(X1) = k2_relat_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(sK6,X1) = sK6
          & k1_relat_1(X1) = k2_relat_1(sK6)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k6_relat_1(k1_relat_1(sK7)) != sK7
    & k5_relat_1(sK6,sK7) = sK6
    & k1_relat_1(sK7) = k2_relat_1(sK6)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f16,f35,f34])).

fof(f58,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    k6_relat_1(k1_relat_1(sK7)) != sK7 ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    k1_relat_1(sK7) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    k5_relat_1(sK6,sK7) = sK6 ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f8])).

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
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
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
              ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21,f20,f19])).

fof(f38,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK5(X0,X1)) != sK5(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK5(k1_relat_1(X1),X1)) != sK5(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f51])).

cnf(c_12,plain,
    ( r2_hidden(sK5(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_324,plain,
    ( r2_hidden(sK5(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_325,plain,
    ( r2_hidden(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k6_relat_1(k1_relat_1(sK7)) = sK7 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( k6_relat_1(k1_relat_1(sK7)) != sK7 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_45,plain,
    ( r2_hidden(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | k6_relat_1(k1_relat_1(sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_327,plain,
    ( r2_hidden(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_22,c_21,c_18,c_45])).

cnf(c_921,plain,
    ( r2_hidden(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_926,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_928,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1382,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_926,c_928])).

cnf(c_20,negated_conjecture,
    ( k1_relat_1(sK7) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1383,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k1_relat_1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_1382,c_20])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_930,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19,negated_conjecture,
    ( k5_relat_1(sK6,sK7) = sK6 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_934,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_430,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_431,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_435,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_22])).

cnf(c_915,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_2135,plain,
    ( k1_funct_1(sK7,sK3(X0,sK7,X1,X2)) = X2
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK7)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_915])).

cnf(c_27,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8064,plain,
    ( v1_relat_1(k5_relat_1(X0,sK7)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK7)) != iProver_top
    | k1_funct_1(sK7,sK3(X0,sK7,X1,X2)) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2135,c_27])).

cnf(c_8065,plain,
    ( k1_funct_1(sK7,sK3(X0,sK7,X1,X2)) = X2
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK7)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8064])).

cnf(c_8075,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7,X0,X1)) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(k5_relat_1(sK6,sK7)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_8065])).

cnf(c_8076,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7,X0,X1)) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8075,c_19])).

cnf(c_25,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8121,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | k1_funct_1(sK7,sK3(sK6,sK7,X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8076,c_25])).

cnf(c_8122,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7,X0,X1)) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_8121])).

cnf(c_8133,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7,sK4(X0,X1,sK6),X0)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_8122])).

cnf(c_8300,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | k1_funct_1(sK7,sK3(sK6,sK7,sK4(X0,X1,sK6),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8133,c_25])).

cnf(c_8301,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7,sK4(X0,X1,sK6),X0)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8300])).

cnf(c_8317,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7,sK4(X0,k1_relat_1(sK6),sK6),X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_8301])).

cnf(c_8432,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK7,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6),sK5(k1_relat_1(sK7),sK7))) = sK5(k1_relat_1(sK7),sK7) ),
    inference(superposition,[status(thm)],[c_921,c_8317])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_933,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_448,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_449,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_453,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_24])).

cnf(c_914,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_2116,plain,
    ( sK3(sK6,X0,X1,X2) = k1_funct_1(sK6,X1)
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_914])).

cnf(c_3877,plain,
    ( v1_relat_1(k5_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK6,X0)) != iProver_top
    | sK3(sK6,X0,X1,X2) = k1_funct_1(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2116,c_25])).

cnf(c_3878,plain,
    ( sK3(sK6,X0,X1,X2) = k1_funct_1(sK6,X1)
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK6,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3877])).

cnf(c_3890,plain,
    ( sK3(sK6,sK7,X0,X1) = k1_funct_1(sK6,X0)
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(k5_relat_1(sK6,sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_3878])).

cnf(c_3891,plain,
    ( sK3(sK6,sK7,X0,X1) = k1_funct_1(sK6,X0)
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3890,c_19])).

cnf(c_3917,plain,
    ( sK3(sK6,sK7,X0,X1) = k1_funct_1(sK6,X0)
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3891,c_25,c_27])).

cnf(c_3929,plain,
    ( sK3(sK6,sK7,sK4(X0,X1,sK6),X0) = k1_funct_1(sK6,sK4(X0,X1,sK6))
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_3917])).

cnf(c_4030,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | sK3(sK6,sK7,sK4(X0,X1,sK6),X0) = k1_funct_1(sK6,sK4(X0,X1,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3929,c_25])).

cnf(c_4031,plain,
    ( sK3(sK6,sK7,sK4(X0,X1,sK6),X0) = k1_funct_1(sK6,sK4(X0,X1,sK6))
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4030])).

cnf(c_4045,plain,
    ( sK3(sK6,sK7,sK4(X0,k1_relat_1(sK6),sK6),X0) = k1_funct_1(sK6,sK4(X0,k1_relat_1(sK6),sK6))
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_4031])).

cnf(c_4184,plain,
    ( sK3(sK6,sK7,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6),sK5(k1_relat_1(sK7),sK7)) = k1_funct_1(sK6,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6)) ),
    inference(superposition,[status(thm)],[c_921,c_4045])).

cnf(c_2005,plain,
    ( k1_funct_1(sK6,sK4(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_914])).

cnf(c_2266,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | k1_funct_1(sK6,sK4(X0,X1,sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2005,c_25])).

cnf(c_2267,plain,
    ( k1_funct_1(sK6,sK4(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2266])).

cnf(c_2276,plain,
    ( k1_funct_1(sK6,sK4(X0,k1_relat_1(sK6),sK6)) = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_2267])).

cnf(c_2298,plain,
    ( k1_funct_1(sK6,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6)) = sK5(k1_relat_1(sK7),sK7) ),
    inference(superposition,[status(thm)],[c_921,c_2276])).

cnf(c_4186,plain,
    ( sK3(sK6,sK7,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6),sK5(k1_relat_1(sK7),sK7)) = sK5(k1_relat_1(sK7),sK7) ),
    inference(light_normalisation,[status(thm)],[c_4184,c_2298])).

cnf(c_8438,plain,
    ( k1_funct_1(sK7,sK5(k1_relat_1(sK7),sK7)) = sK5(k1_relat_1(sK7),sK7) ),
    inference(light_normalisation,[status(thm)],[c_8432,c_4186])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK5(k1_relat_1(X0),X0)) != sK5(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_48,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK5(k1_relat_1(sK7),sK7)) != sK5(k1_relat_1(sK7),sK7)
    | k6_relat_1(k1_relat_1(sK7)) = sK7 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8438,c_48,c_18,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.60/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.01  
% 3.60/1.01  ------  iProver source info
% 3.60/1.01  
% 3.60/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.01  git: non_committed_changes: false
% 3.60/1.01  git: last_make_outside_of_git: false
% 3.60/1.01  
% 3.60/1.01  ------ 
% 3.60/1.01  
% 3.60/1.01  ------ Input Options
% 3.60/1.01  
% 3.60/1.01  --out_options                           all
% 3.60/1.01  --tptp_safe_out                         true
% 3.60/1.01  --problem_path                          ""
% 3.60/1.01  --include_path                          ""
% 3.60/1.01  --clausifier                            res/vclausify_rel
% 3.60/1.01  --clausifier_options                    ""
% 3.60/1.01  --stdin                                 false
% 3.60/1.01  --stats_out                             all
% 3.60/1.01  
% 3.60/1.01  ------ General Options
% 3.60/1.01  
% 3.60/1.01  --fof                                   false
% 3.60/1.01  --time_out_real                         305.
% 3.60/1.01  --time_out_virtual                      -1.
% 3.60/1.01  --symbol_type_check                     false
% 3.60/1.01  --clausify_out                          false
% 3.60/1.01  --sig_cnt_out                           false
% 3.60/1.01  --trig_cnt_out                          false
% 3.60/1.01  --trig_cnt_out_tolerance                1.
% 3.60/1.01  --trig_cnt_out_sk_spl                   false
% 3.60/1.01  --abstr_cl_out                          false
% 3.60/1.01  
% 3.60/1.01  ------ Global Options
% 3.60/1.01  
% 3.60/1.01  --schedule                              default
% 3.60/1.01  --add_important_lit                     false
% 3.60/1.01  --prop_solver_per_cl                    1000
% 3.60/1.01  --min_unsat_core                        false
% 3.60/1.01  --soft_assumptions                      false
% 3.60/1.01  --soft_lemma_size                       3
% 3.60/1.01  --prop_impl_unit_size                   0
% 3.60/1.01  --prop_impl_unit                        []
% 3.60/1.01  --share_sel_clauses                     true
% 3.60/1.01  --reset_solvers                         false
% 3.60/1.01  --bc_imp_inh                            [conj_cone]
% 3.60/1.01  --conj_cone_tolerance                   3.
% 3.60/1.01  --extra_neg_conj                        none
% 3.60/1.01  --large_theory_mode                     true
% 3.60/1.01  --prolific_symb_bound                   200
% 3.60/1.01  --lt_threshold                          2000
% 3.60/1.01  --clause_weak_htbl                      true
% 3.60/1.01  --gc_record_bc_elim                     false
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing Options
% 3.60/1.01  
% 3.60/1.01  --preprocessing_flag                    true
% 3.60/1.01  --time_out_prep_mult                    0.1
% 3.60/1.01  --splitting_mode                        input
% 3.60/1.01  --splitting_grd                         true
% 3.60/1.01  --splitting_cvd                         false
% 3.60/1.01  --splitting_cvd_svl                     false
% 3.60/1.01  --splitting_nvd                         32
% 3.60/1.01  --sub_typing                            true
% 3.60/1.01  --prep_gs_sim                           true
% 3.60/1.01  --prep_unflatten                        true
% 3.60/1.01  --prep_res_sim                          true
% 3.60/1.01  --prep_upred                            true
% 3.60/1.01  --prep_sem_filter                       exhaustive
% 3.60/1.01  --prep_sem_filter_out                   false
% 3.60/1.01  --pred_elim                             true
% 3.60/1.01  --res_sim_input                         true
% 3.60/1.01  --eq_ax_congr_red                       true
% 3.60/1.01  --pure_diseq_elim                       true
% 3.60/1.01  --brand_transform                       false
% 3.60/1.01  --non_eq_to_eq                          false
% 3.60/1.01  --prep_def_merge                        true
% 3.60/1.01  --prep_def_merge_prop_impl              false
% 3.60/1.01  --prep_def_merge_mbd                    true
% 3.60/1.01  --prep_def_merge_tr_red                 false
% 3.60/1.01  --prep_def_merge_tr_cl                  false
% 3.60/1.01  --smt_preprocessing                     true
% 3.60/1.01  --smt_ac_axioms                         fast
% 3.60/1.01  --preprocessed_out                      false
% 3.60/1.01  --preprocessed_stats                    false
% 3.60/1.01  
% 3.60/1.01  ------ Abstraction refinement Options
% 3.60/1.01  
% 3.60/1.01  --abstr_ref                             []
% 3.60/1.01  --abstr_ref_prep                        false
% 3.60/1.01  --abstr_ref_until_sat                   false
% 3.60/1.01  --abstr_ref_sig_restrict                funpre
% 3.60/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.01  --abstr_ref_under                       []
% 3.60/1.01  
% 3.60/1.01  ------ SAT Options
% 3.60/1.01  
% 3.60/1.01  --sat_mode                              false
% 3.60/1.01  --sat_fm_restart_options                ""
% 3.60/1.01  --sat_gr_def                            false
% 3.60/1.01  --sat_epr_types                         true
% 3.60/1.01  --sat_non_cyclic_types                  false
% 3.60/1.01  --sat_finite_models                     false
% 3.60/1.01  --sat_fm_lemmas                         false
% 3.60/1.01  --sat_fm_prep                           false
% 3.60/1.01  --sat_fm_uc_incr                        true
% 3.60/1.01  --sat_out_model                         small
% 3.60/1.01  --sat_out_clauses                       false
% 3.60/1.01  
% 3.60/1.01  ------ QBF Options
% 3.60/1.01  
% 3.60/1.01  --qbf_mode                              false
% 3.60/1.01  --qbf_elim_univ                         false
% 3.60/1.01  --qbf_dom_inst                          none
% 3.60/1.01  --qbf_dom_pre_inst                      false
% 3.60/1.01  --qbf_sk_in                             false
% 3.60/1.01  --qbf_pred_elim                         true
% 3.60/1.01  --qbf_split                             512
% 3.60/1.01  
% 3.60/1.01  ------ BMC1 Options
% 3.60/1.01  
% 3.60/1.01  --bmc1_incremental                      false
% 3.60/1.01  --bmc1_axioms                           reachable_all
% 3.60/1.01  --bmc1_min_bound                        0
% 3.60/1.01  --bmc1_max_bound                        -1
% 3.60/1.01  --bmc1_max_bound_default                -1
% 3.60/1.01  --bmc1_symbol_reachability              true
% 3.60/1.01  --bmc1_property_lemmas                  false
% 3.60/1.01  --bmc1_k_induction                      false
% 3.60/1.01  --bmc1_non_equiv_states                 false
% 3.60/1.01  --bmc1_deadlock                         false
% 3.60/1.01  --bmc1_ucm                              false
% 3.60/1.01  --bmc1_add_unsat_core                   none
% 3.60/1.01  --bmc1_unsat_core_children              false
% 3.60/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.01  --bmc1_out_stat                         full
% 3.60/1.01  --bmc1_ground_init                      false
% 3.60/1.01  --bmc1_pre_inst_next_state              false
% 3.60/1.01  --bmc1_pre_inst_state                   false
% 3.60/1.01  --bmc1_pre_inst_reach_state             false
% 3.60/1.01  --bmc1_out_unsat_core                   false
% 3.60/1.01  --bmc1_aig_witness_out                  false
% 3.60/1.01  --bmc1_verbose                          false
% 3.60/1.01  --bmc1_dump_clauses_tptp                false
% 3.60/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.01  --bmc1_dump_file                        -
% 3.60/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.01  --bmc1_ucm_extend_mode                  1
% 3.60/1.01  --bmc1_ucm_init_mode                    2
% 3.60/1.01  --bmc1_ucm_cone_mode                    none
% 3.60/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.01  --bmc1_ucm_relax_model                  4
% 3.60/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.01  --bmc1_ucm_layered_model                none
% 3.60/1.01  --bmc1_ucm_max_lemma_size               10
% 3.60/1.01  
% 3.60/1.01  ------ AIG Options
% 3.60/1.01  
% 3.60/1.01  --aig_mode                              false
% 3.60/1.01  
% 3.60/1.01  ------ Instantiation Options
% 3.60/1.01  
% 3.60/1.01  --instantiation_flag                    true
% 3.60/1.01  --inst_sos_flag                         true
% 3.60/1.01  --inst_sos_phase                        true
% 3.60/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.01  --inst_lit_sel_side                     num_symb
% 3.60/1.01  --inst_solver_per_active                1400
% 3.60/1.01  --inst_solver_calls_frac                1.
% 3.60/1.01  --inst_passive_queue_type               priority_queues
% 3.60/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.01  --inst_passive_queues_freq              [25;2]
% 3.60/1.01  --inst_dismatching                      true
% 3.60/1.01  --inst_eager_unprocessed_to_passive     true
% 3.60/1.01  --inst_prop_sim_given                   true
% 3.60/1.01  --inst_prop_sim_new                     false
% 3.60/1.01  --inst_subs_new                         false
% 3.60/1.01  --inst_eq_res_simp                      false
% 3.60/1.01  --inst_subs_given                       false
% 3.60/1.01  --inst_orphan_elimination               true
% 3.60/1.01  --inst_learning_loop_flag               true
% 3.60/1.01  --inst_learning_start                   3000
% 3.60/1.01  --inst_learning_factor                  2
% 3.60/1.01  --inst_start_prop_sim_after_learn       3
% 3.60/1.01  --inst_sel_renew                        solver
% 3.60/1.01  --inst_lit_activity_flag                true
% 3.60/1.01  --inst_restr_to_given                   false
% 3.60/1.01  --inst_activity_threshold               500
% 3.60/1.01  --inst_out_proof                        true
% 3.60/1.01  
% 3.60/1.01  ------ Resolution Options
% 3.60/1.01  
% 3.60/1.01  --resolution_flag                       true
% 3.60/1.01  --res_lit_sel                           adaptive
% 3.60/1.01  --res_lit_sel_side                      none
% 3.60/1.01  --res_ordering                          kbo
% 3.60/1.01  --res_to_prop_solver                    active
% 3.60/1.01  --res_prop_simpl_new                    false
% 3.60/1.01  --res_prop_simpl_given                  true
% 3.60/1.01  --res_passive_queue_type                priority_queues
% 3.60/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.01  --res_passive_queues_freq               [15;5]
% 3.60/1.01  --res_forward_subs                      full
% 3.60/1.01  --res_backward_subs                     full
% 3.60/1.01  --res_forward_subs_resolution           true
% 3.60/1.01  --res_backward_subs_resolution          true
% 3.60/1.01  --res_orphan_elimination                true
% 3.60/1.01  --res_time_limit                        2.
% 3.60/1.01  --res_out_proof                         true
% 3.60/1.01  
% 3.60/1.01  ------ Superposition Options
% 3.60/1.01  
% 3.60/1.01  --superposition_flag                    true
% 3.60/1.01  --sup_passive_queue_type                priority_queues
% 3.60/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.01  --demod_completeness_check              fast
% 3.60/1.01  --demod_use_ground                      true
% 3.60/1.01  --sup_to_prop_solver                    passive
% 3.60/1.01  --sup_prop_simpl_new                    true
% 3.60/1.01  --sup_prop_simpl_given                  true
% 3.60/1.01  --sup_fun_splitting                     true
% 3.60/1.01  --sup_smt_interval                      50000
% 3.60/1.01  
% 3.60/1.01  ------ Superposition Simplification Setup
% 3.60/1.01  
% 3.60/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.60/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.60/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.60/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.60/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.60/1.01  --sup_immed_triv                        [TrivRules]
% 3.60/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.01  --sup_immed_bw_main                     []
% 3.60/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.60/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.01  --sup_input_bw                          []
% 3.60/1.01  
% 3.60/1.01  ------ Combination Options
% 3.60/1.01  
% 3.60/1.01  --comb_res_mult                         3
% 3.60/1.01  --comb_sup_mult                         2
% 3.60/1.01  --comb_inst_mult                        10
% 3.60/1.01  
% 3.60/1.01  ------ Debug Options
% 3.60/1.01  
% 3.60/1.01  --dbg_backtrace                         false
% 3.60/1.01  --dbg_dump_prop_clauses                 false
% 3.60/1.01  --dbg_dump_prop_clauses_file            -
% 3.60/1.01  --dbg_out_stat                          false
% 3.60/1.01  ------ Parsing...
% 3.60/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.01  ------ Proving...
% 3.60/1.01  ------ Problem Properties 
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  clauses                                 30
% 3.60/1.01  conjectures                             5
% 3.60/1.01  EPR                                     2
% 3.60/1.01  Horn                                    27
% 3.60/1.01  unary                                   7
% 3.60/1.01  binary                                  9
% 3.60/1.01  lits                                    88
% 3.60/1.01  lits eq                                 21
% 3.60/1.01  fd_pure                                 0
% 3.60/1.01  fd_pseudo                               0
% 3.60/1.01  fd_cond                                 0
% 3.60/1.01  fd_pseudo_cond                          5
% 3.60/1.01  AC symbols                              0
% 3.60/1.01  
% 3.60/1.01  ------ Schedule dynamic 5 is on 
% 3.60/1.01  
% 3.60/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  ------ 
% 3.60/1.01  Current options:
% 3.60/1.01  ------ 
% 3.60/1.01  
% 3.60/1.01  ------ Input Options
% 3.60/1.01  
% 3.60/1.01  --out_options                           all
% 3.60/1.01  --tptp_safe_out                         true
% 3.60/1.01  --problem_path                          ""
% 3.60/1.01  --include_path                          ""
% 3.60/1.01  --clausifier                            res/vclausify_rel
% 3.60/1.01  --clausifier_options                    ""
% 3.60/1.01  --stdin                                 false
% 3.60/1.01  --stats_out                             all
% 3.60/1.01  
% 3.60/1.01  ------ General Options
% 3.60/1.01  
% 3.60/1.01  --fof                                   false
% 3.60/1.01  --time_out_real                         305.
% 3.60/1.01  --time_out_virtual                      -1.
% 3.60/1.01  --symbol_type_check                     false
% 3.60/1.01  --clausify_out                          false
% 3.60/1.01  --sig_cnt_out                           false
% 3.60/1.01  --trig_cnt_out                          false
% 3.60/1.01  --trig_cnt_out_tolerance                1.
% 3.60/1.01  --trig_cnt_out_sk_spl                   false
% 3.60/1.01  --abstr_cl_out                          false
% 3.60/1.01  
% 3.60/1.01  ------ Global Options
% 3.60/1.01  
% 3.60/1.01  --schedule                              default
% 3.60/1.01  --add_important_lit                     false
% 3.60/1.01  --prop_solver_per_cl                    1000
% 3.60/1.01  --min_unsat_core                        false
% 3.60/1.01  --soft_assumptions                      false
% 3.60/1.01  --soft_lemma_size                       3
% 3.60/1.01  --prop_impl_unit_size                   0
% 3.60/1.01  --prop_impl_unit                        []
% 3.60/1.01  --share_sel_clauses                     true
% 3.60/1.01  --reset_solvers                         false
% 3.60/1.01  --bc_imp_inh                            [conj_cone]
% 3.60/1.01  --conj_cone_tolerance                   3.
% 3.60/1.01  --extra_neg_conj                        none
% 3.60/1.01  --large_theory_mode                     true
% 3.60/1.01  --prolific_symb_bound                   200
% 3.60/1.01  --lt_threshold                          2000
% 3.60/1.01  --clause_weak_htbl                      true
% 3.60/1.01  --gc_record_bc_elim                     false
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing Options
% 3.60/1.01  
% 3.60/1.01  --preprocessing_flag                    true
% 3.60/1.01  --time_out_prep_mult                    0.1
% 3.60/1.01  --splitting_mode                        input
% 3.60/1.01  --splitting_grd                         true
% 3.60/1.01  --splitting_cvd                         false
% 3.60/1.01  --splitting_cvd_svl                     false
% 3.60/1.01  --splitting_nvd                         32
% 3.60/1.01  --sub_typing                            true
% 3.60/1.01  --prep_gs_sim                           true
% 3.60/1.01  --prep_unflatten                        true
% 3.60/1.01  --prep_res_sim                          true
% 3.60/1.01  --prep_upred                            true
% 3.60/1.01  --prep_sem_filter                       exhaustive
% 3.60/1.01  --prep_sem_filter_out                   false
% 3.60/1.01  --pred_elim                             true
% 3.60/1.01  --res_sim_input                         true
% 3.60/1.01  --eq_ax_congr_red                       true
% 3.60/1.01  --pure_diseq_elim                       true
% 3.60/1.01  --brand_transform                       false
% 3.60/1.01  --non_eq_to_eq                          false
% 3.60/1.01  --prep_def_merge                        true
% 3.60/1.01  --prep_def_merge_prop_impl              false
% 3.60/1.01  --prep_def_merge_mbd                    true
% 3.60/1.01  --prep_def_merge_tr_red                 false
% 3.60/1.01  --prep_def_merge_tr_cl                  false
% 3.60/1.01  --smt_preprocessing                     true
% 3.60/1.01  --smt_ac_axioms                         fast
% 3.60/1.01  --preprocessed_out                      false
% 3.60/1.01  --preprocessed_stats                    false
% 3.60/1.01  
% 3.60/1.01  ------ Abstraction refinement Options
% 3.60/1.01  
% 3.60/1.01  --abstr_ref                             []
% 3.60/1.01  --abstr_ref_prep                        false
% 3.60/1.01  --abstr_ref_until_sat                   false
% 3.60/1.01  --abstr_ref_sig_restrict                funpre
% 3.60/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.01  --abstr_ref_under                       []
% 3.60/1.01  
% 3.60/1.01  ------ SAT Options
% 3.60/1.01  
% 3.60/1.01  --sat_mode                              false
% 3.60/1.01  --sat_fm_restart_options                ""
% 3.60/1.01  --sat_gr_def                            false
% 3.60/1.01  --sat_epr_types                         true
% 3.60/1.01  --sat_non_cyclic_types                  false
% 3.60/1.01  --sat_finite_models                     false
% 3.60/1.01  --sat_fm_lemmas                         false
% 3.60/1.01  --sat_fm_prep                           false
% 3.60/1.01  --sat_fm_uc_incr                        true
% 3.60/1.01  --sat_out_model                         small
% 3.60/1.01  --sat_out_clauses                       false
% 3.60/1.01  
% 3.60/1.01  ------ QBF Options
% 3.60/1.01  
% 3.60/1.01  --qbf_mode                              false
% 3.60/1.01  --qbf_elim_univ                         false
% 3.60/1.01  --qbf_dom_inst                          none
% 3.60/1.01  --qbf_dom_pre_inst                      false
% 3.60/1.01  --qbf_sk_in                             false
% 3.60/1.01  --qbf_pred_elim                         true
% 3.60/1.01  --qbf_split                             512
% 3.60/1.01  
% 3.60/1.01  ------ BMC1 Options
% 3.60/1.01  
% 3.60/1.01  --bmc1_incremental                      false
% 3.60/1.01  --bmc1_axioms                           reachable_all
% 3.60/1.01  --bmc1_min_bound                        0
% 3.60/1.01  --bmc1_max_bound                        -1
% 3.60/1.01  --bmc1_max_bound_default                -1
% 3.60/1.01  --bmc1_symbol_reachability              true
% 3.60/1.01  --bmc1_property_lemmas                  false
% 3.60/1.01  --bmc1_k_induction                      false
% 3.60/1.01  --bmc1_non_equiv_states                 false
% 3.60/1.01  --bmc1_deadlock                         false
% 3.60/1.01  --bmc1_ucm                              false
% 3.60/1.01  --bmc1_add_unsat_core                   none
% 3.60/1.01  --bmc1_unsat_core_children              false
% 3.60/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.01  --bmc1_out_stat                         full
% 3.60/1.01  --bmc1_ground_init                      false
% 3.60/1.01  --bmc1_pre_inst_next_state              false
% 3.60/1.01  --bmc1_pre_inst_state                   false
% 3.60/1.01  --bmc1_pre_inst_reach_state             false
% 3.60/1.01  --bmc1_out_unsat_core                   false
% 3.60/1.01  --bmc1_aig_witness_out                  false
% 3.60/1.01  --bmc1_verbose                          false
% 3.60/1.01  --bmc1_dump_clauses_tptp                false
% 3.60/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.01  --bmc1_dump_file                        -
% 3.60/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.01  --bmc1_ucm_extend_mode                  1
% 3.60/1.01  --bmc1_ucm_init_mode                    2
% 3.60/1.01  --bmc1_ucm_cone_mode                    none
% 3.60/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.01  --bmc1_ucm_relax_model                  4
% 3.60/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.01  --bmc1_ucm_layered_model                none
% 3.60/1.01  --bmc1_ucm_max_lemma_size               10
% 3.60/1.01  
% 3.60/1.01  ------ AIG Options
% 3.60/1.01  
% 3.60/1.01  --aig_mode                              false
% 3.60/1.01  
% 3.60/1.01  ------ Instantiation Options
% 3.60/1.01  
% 3.60/1.01  --instantiation_flag                    true
% 3.60/1.01  --inst_sos_flag                         true
% 3.60/1.01  --inst_sos_phase                        true
% 3.60/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.01  --inst_lit_sel_side                     none
% 3.60/1.01  --inst_solver_per_active                1400
% 3.60/1.01  --inst_solver_calls_frac                1.
% 3.60/1.01  --inst_passive_queue_type               priority_queues
% 3.60/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.01  --inst_passive_queues_freq              [25;2]
% 3.60/1.01  --inst_dismatching                      true
% 3.60/1.01  --inst_eager_unprocessed_to_passive     true
% 3.60/1.01  --inst_prop_sim_given                   true
% 3.60/1.01  --inst_prop_sim_new                     false
% 3.60/1.01  --inst_subs_new                         false
% 3.60/1.01  --inst_eq_res_simp                      false
% 3.60/1.01  --inst_subs_given                       false
% 3.60/1.01  --inst_orphan_elimination               true
% 3.60/1.01  --inst_learning_loop_flag               true
% 3.60/1.01  --inst_learning_start                   3000
% 3.60/1.01  --inst_learning_factor                  2
% 3.60/1.01  --inst_start_prop_sim_after_learn       3
% 3.60/1.01  --inst_sel_renew                        solver
% 3.60/1.01  --inst_lit_activity_flag                true
% 3.60/1.01  --inst_restr_to_given                   false
% 3.60/1.01  --inst_activity_threshold               500
% 3.60/1.01  --inst_out_proof                        true
% 3.60/1.01  
% 3.60/1.01  ------ Resolution Options
% 3.60/1.01  
% 3.60/1.01  --resolution_flag                       false
% 3.60/1.01  --res_lit_sel                           adaptive
% 3.60/1.01  --res_lit_sel_side                      none
% 3.60/1.01  --res_ordering                          kbo
% 3.60/1.01  --res_to_prop_solver                    active
% 3.60/1.01  --res_prop_simpl_new                    false
% 3.60/1.01  --res_prop_simpl_given                  true
% 3.60/1.01  --res_passive_queue_type                priority_queues
% 3.60/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.01  --res_passive_queues_freq               [15;5]
% 3.60/1.01  --res_forward_subs                      full
% 3.60/1.01  --res_backward_subs                     full
% 3.60/1.01  --res_forward_subs_resolution           true
% 3.60/1.01  --res_backward_subs_resolution          true
% 3.60/1.01  --res_orphan_elimination                true
% 3.60/1.01  --res_time_limit                        2.
% 3.60/1.01  --res_out_proof                         true
% 3.60/1.01  
% 3.60/1.01  ------ Superposition Options
% 3.60/1.01  
% 3.60/1.01  --superposition_flag                    true
% 3.60/1.01  --sup_passive_queue_type                priority_queues
% 3.60/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.01  --demod_completeness_check              fast
% 3.60/1.01  --demod_use_ground                      true
% 3.60/1.01  --sup_to_prop_solver                    passive
% 3.60/1.01  --sup_prop_simpl_new                    true
% 3.60/1.01  --sup_prop_simpl_given                  true
% 3.60/1.01  --sup_fun_splitting                     true
% 3.60/1.01  --sup_smt_interval                      50000
% 3.60/1.01  
% 3.60/1.01  ------ Superposition Simplification Setup
% 3.60/1.01  
% 3.60/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.60/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.60/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.60/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.60/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.60/1.01  --sup_immed_triv                        [TrivRules]
% 3.60/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.01  --sup_immed_bw_main                     []
% 3.60/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.60/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.01  --sup_input_bw                          []
% 3.60/1.01  
% 3.60/1.01  ------ Combination Options
% 3.60/1.01  
% 3.60/1.01  --comb_res_mult                         3
% 3.60/1.01  --comb_sup_mult                         2
% 3.60/1.01  --comb_inst_mult                        10
% 3.60/1.01  
% 3.60/1.01  ------ Debug Options
% 3.60/1.01  
% 3.60/1.01  --dbg_backtrace                         false
% 3.60/1.01  --dbg_dump_prop_clauses                 false
% 3.60/1.01  --dbg_dump_prop_clauses_file            -
% 3.60/1.01  --dbg_out_stat                          false
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  ------ Proving...
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  % SZS status Theorem for theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  fof(f4,axiom,(
% 3.60/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 3.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f11,plain,(
% 3.60/1.01    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.60/1.01    inference(ennf_transformation,[],[f4])).
% 3.60/1.01  
% 3.60/1.01  fof(f12,plain,(
% 3.60/1.01    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.60/1.01    inference(flattening,[],[f11])).
% 3.60/1.01  
% 3.60/1.01  fof(f27,plain,(
% 3.60/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.60/1.01    inference(nnf_transformation,[],[f12])).
% 3.60/1.01  
% 3.60/1.01  fof(f28,plain,(
% 3.60/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.60/1.01    inference(flattening,[],[f27])).
% 3.60/1.01  
% 3.60/1.01  fof(f29,plain,(
% 3.60/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.60/1.01    inference(rectify,[],[f28])).
% 3.60/1.01  
% 3.60/1.01  fof(f30,plain,(
% 3.60/1.01    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK5(X0,X1)) != sK5(X0,X1) & r2_hidden(sK5(X0,X1),X0)))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f31,plain,(
% 3.60/1.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK5(X0,X1)) != sK5(X0,X1) & r2_hidden(sK5(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 3.60/1.01  
% 3.60/1.01  fof(f50,plain,(
% 3.60/1.01    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f31])).
% 3.60/1.01  
% 3.60/1.01  fof(f66,plain,(
% 3.60/1.01    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.60/1.01    inference(equality_resolution,[],[f50])).
% 3.60/1.01  
% 3.60/1.01  fof(f6,conjecture,(
% 3.60/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 3.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f7,negated_conjecture,(
% 3.60/1.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 3.60/1.01    inference(negated_conjecture,[],[f6])).
% 3.60/1.01  
% 3.60/1.01  fof(f15,plain,(
% 3.60/1.01    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.60/1.01    inference(ennf_transformation,[],[f7])).
% 3.60/1.01  
% 3.60/1.01  fof(f16,plain,(
% 3.60/1.01    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.60/1.01    inference(flattening,[],[f15])).
% 3.60/1.01  
% 3.60/1.01  fof(f35,plain,(
% 3.60/1.01    ( ! [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK7)) != sK7 & k5_relat_1(X0,sK7) = X0 & k1_relat_1(sK7) = k2_relat_1(X0) & v1_funct_1(sK7) & v1_relat_1(sK7))) )),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f34,plain,(
% 3.60/1.01    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(sK6,X1) = sK6 & k1_relat_1(X1) = k2_relat_1(sK6) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f36,plain,(
% 3.60/1.01    (k6_relat_1(k1_relat_1(sK7)) != sK7 & k5_relat_1(sK6,sK7) = sK6 & k1_relat_1(sK7) = k2_relat_1(sK6) & v1_funct_1(sK7) & v1_relat_1(sK7)) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f16,f35,f34])).
% 3.60/1.01  
% 3.60/1.01  fof(f58,plain,(
% 3.60/1.01    v1_funct_1(sK7)),
% 3.60/1.01    inference(cnf_transformation,[],[f36])).
% 3.60/1.01  
% 3.60/1.01  fof(f57,plain,(
% 3.60/1.01    v1_relat_1(sK7)),
% 3.60/1.01    inference(cnf_transformation,[],[f36])).
% 3.60/1.01  
% 3.60/1.01  fof(f61,plain,(
% 3.60/1.01    k6_relat_1(k1_relat_1(sK7)) != sK7),
% 3.60/1.01    inference(cnf_transformation,[],[f36])).
% 3.60/1.01  
% 3.60/1.01  fof(f55,plain,(
% 3.60/1.01    v1_relat_1(sK6)),
% 3.60/1.01    inference(cnf_transformation,[],[f36])).
% 3.60/1.01  
% 3.60/1.01  fof(f3,axiom,(
% 3.60/1.01    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f10,plain,(
% 3.60/1.01    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.60/1.01    inference(ennf_transformation,[],[f3])).
% 3.60/1.01  
% 3.60/1.01  fof(f47,plain,(
% 3.60/1.01    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f10])).
% 3.60/1.01  
% 3.60/1.01  fof(f59,plain,(
% 3.60/1.01    k1_relat_1(sK7) = k2_relat_1(sK6)),
% 3.60/1.01    inference(cnf_transformation,[],[f36])).
% 3.60/1.01  
% 3.60/1.01  fof(f2,axiom,(
% 3.60/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f9,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.60/1.01    inference(ennf_transformation,[],[f2])).
% 3.60/1.01  
% 3.60/1.01  fof(f23,plain,(
% 3.60/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.60/1.01    inference(nnf_transformation,[],[f9])).
% 3.60/1.01  
% 3.60/1.01  fof(f24,plain,(
% 3.60/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.60/1.01    inference(rectify,[],[f23])).
% 3.60/1.01  
% 3.60/1.01  fof(f25,plain,(
% 3.60/1.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f26,plain,(
% 3.60/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 3.60/1.01  
% 3.60/1.01  fof(f44,plain,(
% 3.60/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f26])).
% 3.60/1.01  
% 3.60/1.01  fof(f60,plain,(
% 3.60/1.01    k5_relat_1(sK6,sK7) = sK6),
% 3.60/1.01    inference(cnf_transformation,[],[f36])).
% 3.60/1.01  
% 3.60/1.01  fof(f1,axiom,(
% 3.60/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f8,plain,(
% 3.60/1.01    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.60/1.01    inference(ennf_transformation,[],[f1])).
% 3.60/1.01  
% 3.60/1.01  fof(f17,plain,(
% 3.60/1.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.60/1.01    inference(nnf_transformation,[],[f8])).
% 3.60/1.01  
% 3.60/1.01  fof(f18,plain,(
% 3.60/1.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.60/1.01    inference(rectify,[],[f17])).
% 3.60/1.01  
% 3.60/1.01  fof(f21,plain,(
% 3.60/1.01    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f20,plain,(
% 3.60/1.01    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f19,plain,(
% 3.60/1.01    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 3.60/1.01    introduced(choice_axiom,[])).
% 3.60/1.01  
% 3.60/1.01  fof(f22,plain,(
% 3.60/1.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.60/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21,f20,f19])).
% 3.60/1.01  
% 3.60/1.01  fof(f38,plain,(
% 3.60/1.01    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f22])).
% 3.60/1.01  
% 3.60/1.01  fof(f63,plain,(
% 3.60/1.01    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.60/1.01    inference(equality_resolution,[],[f38])).
% 3.60/1.01  
% 3.60/1.01  fof(f5,axiom,(
% 3.60/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.60/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.01  
% 3.60/1.01  fof(f13,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.60/1.01    inference(ennf_transformation,[],[f5])).
% 3.60/1.01  
% 3.60/1.01  fof(f14,plain,(
% 3.60/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.60/1.01    inference(flattening,[],[f13])).
% 3.60/1.01  
% 3.60/1.01  fof(f32,plain,(
% 3.60/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.60/1.01    inference(nnf_transformation,[],[f14])).
% 3.60/1.01  
% 3.60/1.01  fof(f33,plain,(
% 3.60/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.60/1.01    inference(flattening,[],[f32])).
% 3.60/1.01  
% 3.60/1.01  fof(f53,plain,(
% 3.60/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f33])).
% 3.60/1.01  
% 3.60/1.01  fof(f37,plain,(
% 3.60/1.01    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f22])).
% 3.60/1.01  
% 3.60/1.01  fof(f64,plain,(
% 3.60/1.01    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.60/1.01    inference(equality_resolution,[],[f37])).
% 3.60/1.01  
% 3.60/1.01  fof(f56,plain,(
% 3.60/1.01    v1_funct_1(sK6)),
% 3.60/1.01    inference(cnf_transformation,[],[f36])).
% 3.60/1.01  
% 3.60/1.01  fof(f51,plain,(
% 3.60/1.01    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK5(X0,X1)) != sK5(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.60/1.01    inference(cnf_transformation,[],[f31])).
% 3.60/1.01  
% 3.60/1.01  fof(f65,plain,(
% 3.60/1.01    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK5(k1_relat_1(X1),X1)) != sK5(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.60/1.01    inference(equality_resolution,[],[f51])).
% 3.60/1.01  
% 3.60/1.01  cnf(c_12,plain,
% 3.60/1.01      ( r2_hidden(sK5(k1_relat_1(X0),X0),k1_relat_1(X0))
% 3.60/1.01      | ~ v1_funct_1(X0)
% 3.60/1.01      | ~ v1_relat_1(X0)
% 3.60/1.01      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 3.60/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_21,negated_conjecture,
% 3.60/1.01      ( v1_funct_1(sK7) ),
% 3.60/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_324,plain,
% 3.60/1.01      ( r2_hidden(sK5(k1_relat_1(X0),X0),k1_relat_1(X0))
% 3.60/1.01      | ~ v1_relat_1(X0)
% 3.60/1.01      | k6_relat_1(k1_relat_1(X0)) = X0
% 3.60/1.01      | sK7 != X0 ),
% 3.60/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_325,plain,
% 3.60/1.01      ( r2_hidden(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK7))
% 3.60/1.01      | ~ v1_relat_1(sK7)
% 3.60/1.01      | k6_relat_1(k1_relat_1(sK7)) = sK7 ),
% 3.60/1.01      inference(unflattening,[status(thm)],[c_324]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_22,negated_conjecture,
% 3.60/1.01      ( v1_relat_1(sK7) ),
% 3.60/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_18,negated_conjecture,
% 3.60/1.01      ( k6_relat_1(k1_relat_1(sK7)) != sK7 ),
% 3.60/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_45,plain,
% 3.60/1.01      ( r2_hidden(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK7))
% 3.60/1.01      | ~ v1_funct_1(sK7)
% 3.60/1.01      | ~ v1_relat_1(sK7)
% 3.60/1.01      | k6_relat_1(k1_relat_1(sK7)) = sK7 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_327,plain,
% 3.60/1.01      ( r2_hidden(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK7)) ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_325,c_22,c_21,c_18,c_45]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_921,plain,
% 3.60/1.01      ( r2_hidden(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK7)) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_24,negated_conjecture,
% 3.60/1.01      ( v1_relat_1(sK6) ),
% 3.60/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_926,plain,
% 3.60/1.01      ( v1_relat_1(sK6) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_10,plain,
% 3.60/1.01      ( ~ v1_relat_1(X0)
% 3.60/1.01      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.60/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_928,plain,
% 3.60/1.01      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.60/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1382,plain,
% 3.60/1.01      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_926,c_928]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_20,negated_conjecture,
% 3.60/1.01      ( k1_relat_1(sK7) = k2_relat_1(sK6) ),
% 3.60/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_1383,plain,
% 3.60/1.01      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k1_relat_1(sK7) ),
% 3.60/1.01      inference(light_normalisation,[status(thm)],[c_1382,c_20]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8,plain,
% 3.60/1.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.60/1.01      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
% 3.60/1.01      | ~ v1_relat_1(X1) ),
% 3.60/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_930,plain,
% 3.60/1.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.60/1.01      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1) = iProver_top
% 3.60/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_19,negated_conjecture,
% 3.60/1.01      ( k5_relat_1(sK6,sK7) = sK6 ),
% 3.60/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.60/1.01      | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3)
% 3.60/1.01      | ~ v1_relat_1(X3)
% 3.60/1.01      | ~ v1_relat_1(X2)
% 3.60/1.01      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_934,plain,
% 3.60/1.01      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.60/1.01      | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3) = iProver_top
% 3.60/1.01      | v1_relat_1(X2) != iProver_top
% 3.60/1.01      | v1_relat_1(X3) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_16,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.60/1.01      | ~ v1_funct_1(X2)
% 3.60/1.01      | ~ v1_relat_1(X2)
% 3.60/1.01      | k1_funct_1(X2,X0) = X1 ),
% 3.60/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_430,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.60/1.01      | ~ v1_relat_1(X2)
% 3.60/1.01      | k1_funct_1(X2,X0) = X1
% 3.60/1.01      | sK7 != X2 ),
% 3.60/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_431,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.60/1.01      | ~ v1_relat_1(sK7)
% 3.60/1.01      | k1_funct_1(sK7,X0) = X1 ),
% 3.60/1.01      inference(unflattening,[status(thm)],[c_430]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_435,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK7) | k1_funct_1(sK7,X0) = X1 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_431,c_22]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_915,plain,
% 3.60/1.01      ( k1_funct_1(sK7,X0) = X1
% 3.60/1.01      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2135,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(X0,sK7,X1,X2)) = X2
% 3.60/1.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK7)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(X0,sK7)) != iProver_top
% 3.60/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_934,c_915]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_27,plain,
% 3.60/1.01      ( v1_relat_1(sK7) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8064,plain,
% 3.60/1.01      ( v1_relat_1(k5_relat_1(X0,sK7)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top
% 3.60/1.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK7)) != iProver_top
% 3.60/1.01      | k1_funct_1(sK7,sK3(X0,sK7,X1,X2)) = X2 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_2135,c_27]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8065,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(X0,sK7,X1,X2)) = X2
% 3.60/1.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK7)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(X0,sK7)) != iProver_top ),
% 3.60/1.01      inference(renaming,[status(thm)],[c_8064]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8075,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(sK6,sK7,X0,X1)) = X1
% 3.60/1.01      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(sK6,sK7)) != iProver_top
% 3.60/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_19,c_8065]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8076,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(sK6,sK7,X0,X1)) = X1
% 3.60/1.01      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.60/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.60/1.01      inference(light_normalisation,[status(thm)],[c_8075,c_19]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_25,plain,
% 3.60/1.01      ( v1_relat_1(sK6) = iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8121,plain,
% 3.60/1.01      ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.60/1.01      | k1_funct_1(sK7,sK3(sK6,sK7,X0,X1)) = X1 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_8076,c_25]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8122,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(sK6,sK7,X0,X1)) = X1
% 3.60/1.01      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 3.60/1.01      inference(renaming,[status(thm)],[c_8121]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8133,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(sK6,sK7,sK4(X0,X1,sK6),X0)) = X0
% 3.60/1.01      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.60/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_930,c_8122]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8300,plain,
% 3.60/1.01      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.60/1.01      | k1_funct_1(sK7,sK3(sK6,sK7,sK4(X0,X1,sK6),X0)) = X0 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_8133,c_25]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8301,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(sK6,sK7,sK4(X0,X1,sK6),X0)) = X0
% 3.60/1.01      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.60/1.01      inference(renaming,[status(thm)],[c_8300]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8317,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(sK6,sK7,sK4(X0,k1_relat_1(sK6),sK6),X0)) = X0
% 3.60/1.01      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1383,c_8301]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8432,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK3(sK6,sK7,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6),sK5(k1_relat_1(sK7),sK7))) = sK5(k1_relat_1(sK7),sK7) ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_921,c_8317]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_5,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 3.60/1.01      | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2)
% 3.60/1.01      | ~ v1_relat_1(X3)
% 3.60/1.01      | ~ v1_relat_1(X2)
% 3.60/1.01      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 3.60/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_933,plain,
% 3.60/1.01      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 3.60/1.01      | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2) = iProver_top
% 3.60/1.01      | v1_relat_1(X2) != iProver_top
% 3.60/1.01      | v1_relat_1(X3) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_23,negated_conjecture,
% 3.60/1.01      ( v1_funct_1(sK6) ),
% 3.60/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_448,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.60/1.01      | ~ v1_relat_1(X2)
% 3.60/1.01      | k1_funct_1(X2,X0) = X1
% 3.60/1.01      | sK6 != X2 ),
% 3.60/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_449,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 3.60/1.01      | ~ v1_relat_1(sK6)
% 3.60/1.01      | k1_funct_1(sK6,X0) = X1 ),
% 3.60/1.01      inference(unflattening,[status(thm)],[c_448]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_453,plain,
% 3.60/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK6) | k1_funct_1(sK6,X0) = X1 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_449,c_24]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_914,plain,
% 3.60/1.01      ( k1_funct_1(sK6,X0) = X1
% 3.60/1.01      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 3.60/1.01      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2116,plain,
% 3.60/1.01      ( sK3(sK6,X0,X1,X2) = k1_funct_1(sK6,X1)
% 3.60/1.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK6,X0)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(sK6,X0)) != iProver_top
% 3.60/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_933,c_914]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3877,plain,
% 3.60/1.01      ( v1_relat_1(k5_relat_1(sK6,X0)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top
% 3.60/1.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK6,X0)) != iProver_top
% 3.60/1.01      | sK3(sK6,X0,X1,X2) = k1_funct_1(sK6,X1) ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_2116,c_25]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3878,plain,
% 3.60/1.01      ( sK3(sK6,X0,X1,X2) = k1_funct_1(sK6,X1)
% 3.60/1.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK6,X0)) != iProver_top
% 3.60/1.01      | v1_relat_1(X0) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(sK6,X0)) != iProver_top ),
% 3.60/1.01      inference(renaming,[status(thm)],[c_3877]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3890,plain,
% 3.60/1.01      ( sK3(sK6,sK7,X0,X1) = k1_funct_1(sK6,X0)
% 3.60/1.01      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.60/1.01      | v1_relat_1(k5_relat_1(sK6,sK7)) != iProver_top
% 3.60/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_19,c_3878]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3891,plain,
% 3.60/1.01      ( sK3(sK6,sK7,X0,X1) = k1_funct_1(sK6,X0)
% 3.60/1.01      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.60/1.01      | v1_relat_1(sK6) != iProver_top
% 3.60/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.60/1.01      inference(light_normalisation,[status(thm)],[c_3890,c_19]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3917,plain,
% 3.60/1.01      ( sK3(sK6,sK7,X0,X1) = k1_funct_1(sK6,X0)
% 3.60/1.01      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_3891,c_25,c_27]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_3929,plain,
% 3.60/1.01      ( sK3(sK6,sK7,sK4(X0,X1,sK6),X0) = k1_funct_1(sK6,sK4(X0,X1,sK6))
% 3.60/1.01      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.60/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_930,c_3917]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4030,plain,
% 3.60/1.01      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.60/1.01      | sK3(sK6,sK7,sK4(X0,X1,sK6),X0) = k1_funct_1(sK6,sK4(X0,X1,sK6)) ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_3929,c_25]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4031,plain,
% 3.60/1.01      ( sK3(sK6,sK7,sK4(X0,X1,sK6),X0) = k1_funct_1(sK6,sK4(X0,X1,sK6))
% 3.60/1.01      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.60/1.01      inference(renaming,[status(thm)],[c_4030]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4045,plain,
% 3.60/1.01      ( sK3(sK6,sK7,sK4(X0,k1_relat_1(sK6),sK6),X0) = k1_funct_1(sK6,sK4(X0,k1_relat_1(sK6),sK6))
% 3.60/1.01      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1383,c_4031]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4184,plain,
% 3.60/1.01      ( sK3(sK6,sK7,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6),sK5(k1_relat_1(sK7),sK7)) = k1_funct_1(sK6,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6)) ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_921,c_4045]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2005,plain,
% 3.60/1.01      ( k1_funct_1(sK6,sK4(X0,X1,sK6)) = X0
% 3.60/1.01      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.60/1.01      | v1_relat_1(sK6) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_930,c_914]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2266,plain,
% 3.60/1.01      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.60/1.01      | k1_funct_1(sK6,sK4(X0,X1,sK6)) = X0 ),
% 3.60/1.01      inference(global_propositional_subsumption,
% 3.60/1.01                [status(thm)],
% 3.60/1.01                [c_2005,c_25]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2267,plain,
% 3.60/1.01      ( k1_funct_1(sK6,sK4(X0,X1,sK6)) = X0
% 3.60/1.01      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.60/1.01      inference(renaming,[status(thm)],[c_2266]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2276,plain,
% 3.60/1.01      ( k1_funct_1(sK6,sK4(X0,k1_relat_1(sK6),sK6)) = X0
% 3.60/1.01      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_1383,c_2267]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_2298,plain,
% 3.60/1.01      ( k1_funct_1(sK6,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6)) = sK5(k1_relat_1(sK7),sK7) ),
% 3.60/1.01      inference(superposition,[status(thm)],[c_921,c_2276]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_4186,plain,
% 3.60/1.01      ( sK3(sK6,sK7,sK4(sK5(k1_relat_1(sK7),sK7),k1_relat_1(sK6),sK6),sK5(k1_relat_1(sK7),sK7)) = sK5(k1_relat_1(sK7),sK7) ),
% 3.60/1.01      inference(light_normalisation,[status(thm)],[c_4184,c_2298]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_8438,plain,
% 3.60/1.01      ( k1_funct_1(sK7,sK5(k1_relat_1(sK7),sK7)) = sK5(k1_relat_1(sK7),sK7) ),
% 3.60/1.01      inference(light_normalisation,[status(thm)],[c_8432,c_4186]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_11,plain,
% 3.60/1.01      ( ~ v1_funct_1(X0)
% 3.60/1.01      | ~ v1_relat_1(X0)
% 3.60/1.01      | k1_funct_1(X0,sK5(k1_relat_1(X0),X0)) != sK5(k1_relat_1(X0),X0)
% 3.60/1.01      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 3.60/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(c_48,plain,
% 3.60/1.01      ( ~ v1_funct_1(sK7)
% 3.60/1.01      | ~ v1_relat_1(sK7)
% 3.60/1.01      | k1_funct_1(sK7,sK5(k1_relat_1(sK7),sK7)) != sK5(k1_relat_1(sK7),sK7)
% 3.60/1.01      | k6_relat_1(k1_relat_1(sK7)) = sK7 ),
% 3.60/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.60/1.01  
% 3.60/1.01  cnf(contradiction,plain,
% 3.60/1.01      ( $false ),
% 3.60/1.01      inference(minisat,[status(thm)],[c_8438,c_48,c_18,c_21,c_22]) ).
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.01  
% 3.60/1.01  ------                               Statistics
% 3.60/1.01  
% 3.60/1.01  ------ General
% 3.60/1.01  
% 3.60/1.01  abstr_ref_over_cycles:                  0
% 3.60/1.01  abstr_ref_under_cycles:                 0
% 3.60/1.01  gc_basic_clause_elim:                   0
% 3.60/1.01  forced_gc_time:                         0
% 3.60/1.01  parsing_time:                           0.022
% 3.60/1.01  unif_index_cands_time:                  0.
% 3.60/1.01  unif_index_add_time:                    0.
% 3.60/1.01  orderings_time:                         0.
% 3.60/1.01  out_proof_time:                         0.012
% 3.60/1.01  total_time:                             0.447
% 3.60/1.01  num_of_symbols:                         49
% 3.60/1.01  num_of_terms:                           16854
% 3.60/1.01  
% 3.60/1.01  ------ Preprocessing
% 3.60/1.01  
% 3.60/1.01  num_of_splits:                          0
% 3.60/1.01  num_of_split_atoms:                     0
% 3.60/1.01  num_of_reused_defs:                     0
% 3.60/1.01  num_eq_ax_congr_red:                    35
% 3.60/1.01  num_of_sem_filtered_clauses:            1
% 3.60/1.01  num_of_subtypes:                        0
% 3.60/1.01  monotx_restored_types:                  0
% 3.60/1.01  sat_num_of_epr_types:                   0
% 3.60/1.01  sat_num_of_non_cyclic_types:            0
% 3.60/1.01  sat_guarded_non_collapsed_types:        0
% 3.60/1.01  num_pure_diseq_elim:                    0
% 3.60/1.01  simp_replaced_by:                       0
% 3.60/1.01  res_preprocessed:                       110
% 3.60/1.01  prep_upred:                             0
% 3.60/1.01  prep_unflattend:                        10
% 3.60/1.01  smt_new_axioms:                         0
% 3.60/1.01  pred_elim_cands:                        3
% 3.60/1.01  pred_elim:                              1
% 3.60/1.01  pred_elim_cl:                           -5
% 3.60/1.01  pred_elim_cycles:                       2
% 3.60/1.01  merged_defs:                            0
% 3.60/1.01  merged_defs_ncl:                        0
% 3.60/1.01  bin_hyper_res:                          0
% 3.60/1.01  prep_cycles:                            3
% 3.60/1.01  pred_elim_time:                         0.004
% 3.60/1.01  splitting_time:                         0.
% 3.60/1.01  sem_filter_time:                        0.
% 3.60/1.01  monotx_time:                            0.
% 3.60/1.01  subtype_inf_time:                       0.
% 3.60/1.01  
% 3.60/1.01  ------ Problem properties
% 3.60/1.01  
% 3.60/1.01  clauses:                                30
% 3.60/1.01  conjectures:                            5
% 3.60/1.01  epr:                                    2
% 3.60/1.01  horn:                                   27
% 3.60/1.01  ground:                                 9
% 3.60/1.01  unary:                                  7
% 3.60/1.01  binary:                                 9
% 3.60/1.01  lits:                                   88
% 3.60/1.01  lits_eq:                                21
% 3.60/1.01  fd_pure:                                0
% 3.60/1.01  fd_pseudo:                              0
% 3.60/1.01  fd_cond:                                0
% 3.60/1.01  fd_pseudo_cond:                         5
% 3.60/1.01  ac_symbols:                             0
% 3.60/1.01  
% 3.60/1.01  ------ Propositional Solver
% 3.60/1.01  
% 3.60/1.01  prop_solver_calls:                      25
% 3.60/1.01  prop_fast_solver_calls:                 1167
% 3.60/1.01  smt_solver_calls:                       0
% 3.60/1.01  smt_fast_solver_calls:                  0
% 3.60/1.01  prop_num_of_clauses:                    5073
% 3.60/1.01  prop_preprocess_simplified:             7533
% 3.60/1.01  prop_fo_subsumed:                       61
% 3.60/1.01  prop_solver_time:                       0.
% 3.60/1.01  smt_solver_time:                        0.
% 3.60/1.01  smt_fast_solver_time:                   0.
% 3.60/1.01  prop_fast_solver_time:                  0.
% 3.60/1.01  prop_unsat_core_time:                   0.
% 3.60/1.01  
% 3.60/1.01  ------ QBF
% 3.60/1.01  
% 3.60/1.01  qbf_q_res:                              0
% 3.60/1.01  qbf_num_tautologies:                    0
% 3.60/1.01  qbf_prep_cycles:                        0
% 3.60/1.01  
% 3.60/1.01  ------ BMC1
% 3.60/1.01  
% 3.60/1.01  bmc1_current_bound:                     -1
% 3.60/1.01  bmc1_last_solved_bound:                 -1
% 3.60/1.01  bmc1_unsat_core_size:                   -1
% 3.60/1.01  bmc1_unsat_core_parents_size:           -1
% 3.60/1.01  bmc1_merge_next_fun:                    0
% 3.60/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.60/1.01  
% 3.60/1.01  ------ Instantiation
% 3.60/1.01  
% 3.60/1.01  inst_num_of_clauses:                    948
% 3.60/1.01  inst_num_in_passive:                    227
% 3.60/1.01  inst_num_in_active:                     476
% 3.60/1.01  inst_num_in_unprocessed:                245
% 3.60/1.01  inst_num_of_loops:                      520
% 3.60/1.01  inst_num_of_learning_restarts:          0
% 3.60/1.01  inst_num_moves_active_passive:          42
% 3.60/1.01  inst_lit_activity:                      0
% 3.60/1.01  inst_lit_activity_moves:                0
% 3.60/1.01  inst_num_tautologies:                   0
% 3.60/1.01  inst_num_prop_implied:                  0
% 3.60/1.01  inst_num_existing_simplified:           0
% 3.60/1.01  inst_num_eq_res_simplified:             0
% 3.60/1.01  inst_num_child_elim:                    0
% 3.60/1.01  inst_num_of_dismatching_blockings:      477
% 3.60/1.01  inst_num_of_non_proper_insts:           747
% 3.60/1.01  inst_num_of_duplicates:                 0
% 3.60/1.01  inst_inst_num_from_inst_to_res:         0
% 3.60/1.01  inst_dismatching_checking_time:         0.
% 3.60/1.01  
% 3.60/1.01  ------ Resolution
% 3.60/1.01  
% 3.60/1.01  res_num_of_clauses:                     0
% 3.60/1.01  res_num_in_passive:                     0
% 3.60/1.01  res_num_in_active:                      0
% 3.60/1.01  res_num_of_loops:                       113
% 3.60/1.01  res_forward_subset_subsumed:            84
% 3.60/1.01  res_backward_subset_subsumed:           0
% 3.60/1.01  res_forward_subsumed:                   0
% 3.60/1.01  res_backward_subsumed:                  0
% 3.60/1.01  res_forward_subsumption_resolution:     0
% 3.60/1.01  res_backward_subsumption_resolution:    0
% 3.60/1.01  res_clause_to_clause_subsumption:       1441
% 3.60/1.01  res_orphan_elimination:                 0
% 3.60/1.01  res_tautology_del:                      99
% 3.60/1.01  res_num_eq_res_simplified:              0
% 3.60/1.01  res_num_sel_changes:                    0
% 3.60/1.01  res_moves_from_active_to_pass:          0
% 3.60/1.01  
% 3.60/1.01  ------ Superposition
% 3.60/1.01  
% 3.60/1.01  sup_time_total:                         0.
% 3.60/1.01  sup_time_generating:                    0.
% 3.60/1.01  sup_time_sim_full:                      0.
% 3.60/1.01  sup_time_sim_immed:                     0.
% 3.60/1.01  
% 3.60/1.01  sup_num_of_clauses:                     609
% 3.60/1.01  sup_num_in_active:                      103
% 3.60/1.01  sup_num_in_passive:                     506
% 3.60/1.01  sup_num_of_loops:                       103
% 3.60/1.01  sup_fw_superposition:                   501
% 3.60/1.01  sup_bw_superposition:                   137
% 3.60/1.01  sup_immediate_simplified:               47
% 3.60/1.01  sup_given_eliminated:                   0
% 3.60/1.01  comparisons_done:                       0
% 3.60/1.01  comparisons_avoided:                    0
% 3.60/1.01  
% 3.60/1.01  ------ Simplifications
% 3.60/1.01  
% 3.60/1.01  
% 3.60/1.01  sim_fw_subset_subsumed:                 7
% 3.60/1.01  sim_bw_subset_subsumed:                 11
% 3.60/1.01  sim_fw_subsumed:                        12
% 3.60/1.01  sim_bw_subsumed:                        1
% 3.60/1.01  sim_fw_subsumption_res:                 0
% 3.60/1.01  sim_bw_subsumption_res:                 0
% 3.60/1.01  sim_tautology_del:                      6
% 3.60/1.01  sim_eq_tautology_del:                   9
% 3.60/1.01  sim_eq_res_simp:                        0
% 3.60/1.01  sim_fw_demodulated:                     0
% 3.60/1.01  sim_bw_demodulated:                     0
% 3.60/1.01  sim_light_normalised:                   37
% 3.60/1.01  sim_joinable_taut:                      0
% 3.60/1.01  sim_joinable_simp:                      0
% 3.60/1.01  sim_ac_normalised:                      0
% 3.60/1.01  sim_smt_subsumption:                    0
% 3.60/1.01  
%------------------------------------------------------------------------------

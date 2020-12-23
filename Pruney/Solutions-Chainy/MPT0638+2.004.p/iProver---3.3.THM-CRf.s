%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:13 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 415 expanded)
%              Number of clauses        :   55 (  91 expanded)
%              Number of leaves         :   14 ( 109 expanded)
%              Depth                    :   26
%              Number of atoms          :  484 (2553 expanded)
%              Number of equality atoms :  187 (1113 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f9])).

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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1)
            & r2_hidden(sK7(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK7(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK7(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k6_relat_1(k1_relat_1(sK9)) != sK9
        & k5_relat_1(X0,sK9) = X0
        & k2_relat_1(X0) = k1_relat_1(sK9)
        & v1_funct_1(sK9)
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X1)) != X1
            & k5_relat_1(X0,X1) = X0
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(sK8,X1) = sK8
          & k2_relat_1(sK8) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k6_relat_1(k1_relat_1(sK9)) != sK9
    & k5_relat_1(sK8,sK9) = sK8
    & k2_relat_1(sK8) = k1_relat_1(sK9)
    & v1_funct_1(sK9)
    & v1_relat_1(sK9)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f13,f34,f33])).

fof(f56,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    k6_relat_1(k1_relat_1(sK9)) != sK9 ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    k2_relat_1(sK8) = k1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f58,plain,(
    k5_relat_1(sK8,sK9) = sK8 ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

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
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
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

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f53,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK7(k1_relat_1(X1),X1)) != sK7(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f49])).

cnf(c_11,plain,
    ( r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_313,plain,
    ( r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_314,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
    | ~ v1_relat_1(sK9)
    | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,negated_conjecture,
    ( k6_relat_1(k1_relat_1(sK9)) != sK9 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_44,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_316,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_21,c_20,c_17,c_44])).

cnf(c_909,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_19,negated_conjecture,
    ( k2_relat_1(sK8) = k1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_937,plain,
    ( r2_hidden(sK7(k2_relat_1(sK8),sK9),k2_relat_1(sK8)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_909,c_19])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_922,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,negated_conjecture,
    ( k5_relat_1(sK8,sK9) = sK8 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_259,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_260,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_264,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
    | ~ r2_hidden(X0,k1_relat_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_260,c_21])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_912,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_972,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_912,c_19])).

cnf(c_7,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_918,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top
    | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2254,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_918])).

cnf(c_26,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2686,plain,
    ( v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2254,c_26])).

cnf(c_2687,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2686])).

cnf(c_2695,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_2687])).

cnf(c_2735,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2695,c_18])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2907,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2735,c_24])).

cnf(c_2908,plain,
    ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_2907])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_923,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2916,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X1)),sK8) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2908,c_923])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_437,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_438,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_23])).

cnf(c_902,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_2923,plain,
    ( k1_funct_1(sK9,X0) = k1_funct_1(sK8,X1)
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2916,c_902])).

cnf(c_5551,plain,
    ( k1_funct_1(sK8,sK2(sK8,X0)) = k1_funct_1(sK9,X0)
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_2923])).

cnf(c_7076,plain,
    ( k1_funct_1(sK8,sK2(sK8,sK7(k2_relat_1(sK8),sK9))) = k1_funct_1(sK9,sK7(k2_relat_1(sK8),sK9)) ),
    inference(superposition,[status(thm)],[c_937,c_5551])).

cnf(c_1417,plain,
    ( k1_funct_1(sK8,sK2(sK8,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_902])).

cnf(c_3030,plain,
    ( k1_funct_1(sK8,sK2(sK8,sK7(k2_relat_1(sK8),sK9))) = sK7(k2_relat_1(sK8),sK9) ),
    inference(superposition,[status(thm)],[c_937,c_1417])).

cnf(c_7197,plain,
    ( k1_funct_1(sK9,sK7(k2_relat_1(sK8),sK9)) = sK7(k2_relat_1(sK8),sK9) ),
    inference(light_normalisation,[status(thm)],[c_7076,c_3030])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK7(k1_relat_1(X0),X0)) != sK7(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_324,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK7(k1_relat_1(X0),X0)) != sK7(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_325,plain,
    ( ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) != sK7(k1_relat_1(sK9),sK9)
    | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_47,plain,
    ( ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) != sK7(k1_relat_1(sK9),sK9)
    | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_327,plain,
    ( k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) != sK7(k1_relat_1(sK9),sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_21,c_20,c_17,c_47])).

cnf(c_940,plain,
    ( k1_funct_1(sK9,sK7(k2_relat_1(sK8),sK9)) != sK7(k2_relat_1(sK8),sK9) ),
    inference(light_normalisation,[status(thm)],[c_327,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7197,c_940])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.27/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/0.98  
% 3.27/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/0.98  
% 3.27/0.98  ------  iProver source info
% 3.27/0.98  
% 3.27/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.27/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/0.98  git: non_committed_changes: false
% 3.27/0.98  git: last_make_outside_of_git: false
% 3.27/0.98  
% 3.27/0.98  ------ 
% 3.27/0.98  
% 3.27/0.98  ------ Input Options
% 3.27/0.98  
% 3.27/0.98  --out_options                           all
% 3.27/0.98  --tptp_safe_out                         true
% 3.27/0.98  --problem_path                          ""
% 3.27/0.98  --include_path                          ""
% 3.27/0.98  --clausifier                            res/vclausify_rel
% 3.27/0.98  --clausifier_options                    --mode clausify
% 3.27/0.98  --stdin                                 false
% 3.27/0.98  --stats_out                             all
% 3.27/0.98  
% 3.27/0.98  ------ General Options
% 3.27/0.98  
% 3.27/0.98  --fof                                   false
% 3.27/0.98  --time_out_real                         305.
% 3.27/0.98  --time_out_virtual                      -1.
% 3.27/0.98  --symbol_type_check                     false
% 3.27/0.98  --clausify_out                          false
% 3.27/0.98  --sig_cnt_out                           false
% 3.27/0.98  --trig_cnt_out                          false
% 3.27/0.98  --trig_cnt_out_tolerance                1.
% 3.27/0.98  --trig_cnt_out_sk_spl                   false
% 3.27/0.98  --abstr_cl_out                          false
% 3.27/0.98  
% 3.27/0.98  ------ Global Options
% 3.27/0.98  
% 3.27/0.98  --schedule                              default
% 3.27/0.98  --add_important_lit                     false
% 3.27/0.98  --prop_solver_per_cl                    1000
% 3.27/0.98  --min_unsat_core                        false
% 3.27/0.98  --soft_assumptions                      false
% 3.27/0.98  --soft_lemma_size                       3
% 3.27/0.98  --prop_impl_unit_size                   0
% 3.27/0.98  --prop_impl_unit                        []
% 3.27/0.98  --share_sel_clauses                     true
% 3.27/0.98  --reset_solvers                         false
% 3.27/0.98  --bc_imp_inh                            [conj_cone]
% 3.27/0.98  --conj_cone_tolerance                   3.
% 3.27/0.98  --extra_neg_conj                        none
% 3.27/0.98  --large_theory_mode                     true
% 3.27/0.98  --prolific_symb_bound                   200
% 3.27/0.98  --lt_threshold                          2000
% 3.27/0.98  --clause_weak_htbl                      true
% 3.27/0.98  --gc_record_bc_elim                     false
% 3.27/0.98  
% 3.27/0.98  ------ Preprocessing Options
% 3.27/0.98  
% 3.27/0.98  --preprocessing_flag                    true
% 3.27/0.98  --time_out_prep_mult                    0.1
% 3.27/0.98  --splitting_mode                        input
% 3.27/0.98  --splitting_grd                         true
% 3.27/0.98  --splitting_cvd                         false
% 3.27/0.98  --splitting_cvd_svl                     false
% 3.27/0.98  --splitting_nvd                         32
% 3.27/0.98  --sub_typing                            true
% 3.27/0.98  --prep_gs_sim                           true
% 3.27/0.98  --prep_unflatten                        true
% 3.27/0.98  --prep_res_sim                          true
% 3.27/0.98  --prep_upred                            true
% 3.27/0.98  --prep_sem_filter                       exhaustive
% 3.27/0.98  --prep_sem_filter_out                   false
% 3.27/0.98  --pred_elim                             true
% 3.27/0.98  --res_sim_input                         true
% 3.27/0.98  --eq_ax_congr_red                       true
% 3.27/0.98  --pure_diseq_elim                       true
% 3.27/0.98  --brand_transform                       false
% 3.27/0.98  --non_eq_to_eq                          false
% 3.27/0.98  --prep_def_merge                        true
% 3.27/0.98  --prep_def_merge_prop_impl              false
% 3.27/0.98  --prep_def_merge_mbd                    true
% 3.27/0.98  --prep_def_merge_tr_red                 false
% 3.27/0.98  --prep_def_merge_tr_cl                  false
% 3.27/0.98  --smt_preprocessing                     true
% 3.27/0.98  --smt_ac_axioms                         fast
% 3.27/0.98  --preprocessed_out                      false
% 3.27/0.98  --preprocessed_stats                    false
% 3.27/0.98  
% 3.27/0.98  ------ Abstraction refinement Options
% 3.27/0.98  
% 3.27/0.98  --abstr_ref                             []
% 3.27/0.98  --abstr_ref_prep                        false
% 3.27/0.98  --abstr_ref_until_sat                   false
% 3.27/0.98  --abstr_ref_sig_restrict                funpre
% 3.27/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.98  --abstr_ref_under                       []
% 3.27/0.98  
% 3.27/0.98  ------ SAT Options
% 3.27/0.98  
% 3.27/0.98  --sat_mode                              false
% 3.27/0.98  --sat_fm_restart_options                ""
% 3.27/0.98  --sat_gr_def                            false
% 3.27/0.98  --sat_epr_types                         true
% 3.27/0.98  --sat_non_cyclic_types                  false
% 3.27/0.98  --sat_finite_models                     false
% 3.27/0.98  --sat_fm_lemmas                         false
% 3.27/0.98  --sat_fm_prep                           false
% 3.27/0.98  --sat_fm_uc_incr                        true
% 3.27/0.98  --sat_out_model                         small
% 3.27/0.98  --sat_out_clauses                       false
% 3.27/0.98  
% 3.27/0.98  ------ QBF Options
% 3.27/0.98  
% 3.27/0.98  --qbf_mode                              false
% 3.27/0.98  --qbf_elim_univ                         false
% 3.27/0.98  --qbf_dom_inst                          none
% 3.27/0.98  --qbf_dom_pre_inst                      false
% 3.27/0.98  --qbf_sk_in                             false
% 3.27/0.98  --qbf_pred_elim                         true
% 3.27/0.98  --qbf_split                             512
% 3.27/0.98  
% 3.27/0.98  ------ BMC1 Options
% 3.27/0.98  
% 3.27/0.98  --bmc1_incremental                      false
% 3.27/0.98  --bmc1_axioms                           reachable_all
% 3.27/0.98  --bmc1_min_bound                        0
% 3.27/0.98  --bmc1_max_bound                        -1
% 3.27/0.98  --bmc1_max_bound_default                -1
% 3.27/0.98  --bmc1_symbol_reachability              true
% 3.27/0.98  --bmc1_property_lemmas                  false
% 3.27/0.98  --bmc1_k_induction                      false
% 3.27/0.98  --bmc1_non_equiv_states                 false
% 3.27/0.98  --bmc1_deadlock                         false
% 3.27/0.98  --bmc1_ucm                              false
% 3.27/0.98  --bmc1_add_unsat_core                   none
% 3.27/0.98  --bmc1_unsat_core_children              false
% 3.27/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.98  --bmc1_out_stat                         full
% 3.27/0.98  --bmc1_ground_init                      false
% 3.27/0.98  --bmc1_pre_inst_next_state              false
% 3.27/0.98  --bmc1_pre_inst_state                   false
% 3.27/0.98  --bmc1_pre_inst_reach_state             false
% 3.27/0.98  --bmc1_out_unsat_core                   false
% 3.27/0.98  --bmc1_aig_witness_out                  false
% 3.27/0.98  --bmc1_verbose                          false
% 3.27/0.98  --bmc1_dump_clauses_tptp                false
% 3.27/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.98  --bmc1_dump_file                        -
% 3.27/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.98  --bmc1_ucm_extend_mode                  1
% 3.27/0.98  --bmc1_ucm_init_mode                    2
% 3.27/0.98  --bmc1_ucm_cone_mode                    none
% 3.27/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.98  --bmc1_ucm_relax_model                  4
% 3.27/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.98  --bmc1_ucm_layered_model                none
% 3.27/0.98  --bmc1_ucm_max_lemma_size               10
% 3.27/0.98  
% 3.27/0.98  ------ AIG Options
% 3.27/0.98  
% 3.27/0.98  --aig_mode                              false
% 3.27/0.98  
% 3.27/0.98  ------ Instantiation Options
% 3.27/0.98  
% 3.27/0.98  --instantiation_flag                    true
% 3.27/0.98  --inst_sos_flag                         false
% 3.27/0.98  --inst_sos_phase                        true
% 3.27/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.98  --inst_lit_sel_side                     num_symb
% 3.27/0.98  --inst_solver_per_active                1400
% 3.27/0.98  --inst_solver_calls_frac                1.
% 3.27/0.98  --inst_passive_queue_type               priority_queues
% 3.27/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.98  --inst_passive_queues_freq              [25;2]
% 3.27/0.98  --inst_dismatching                      true
% 3.27/0.98  --inst_eager_unprocessed_to_passive     true
% 3.27/0.98  --inst_prop_sim_given                   true
% 3.27/0.98  --inst_prop_sim_new                     false
% 3.27/0.98  --inst_subs_new                         false
% 3.27/0.98  --inst_eq_res_simp                      false
% 3.27/0.98  --inst_subs_given                       false
% 3.27/0.98  --inst_orphan_elimination               true
% 3.27/0.98  --inst_learning_loop_flag               true
% 3.27/0.98  --inst_learning_start                   3000
% 3.27/0.98  --inst_learning_factor                  2
% 3.27/0.98  --inst_start_prop_sim_after_learn       3
% 3.27/0.98  --inst_sel_renew                        solver
% 3.27/0.98  --inst_lit_activity_flag                true
% 3.27/0.98  --inst_restr_to_given                   false
% 3.27/0.98  --inst_activity_threshold               500
% 3.27/0.98  --inst_out_proof                        true
% 3.27/0.98  
% 3.27/0.98  ------ Resolution Options
% 3.27/0.98  
% 3.27/0.98  --resolution_flag                       true
% 3.27/0.98  --res_lit_sel                           adaptive
% 3.27/0.98  --res_lit_sel_side                      none
% 3.27/0.98  --res_ordering                          kbo
% 3.27/0.98  --res_to_prop_solver                    active
% 3.27/0.98  --res_prop_simpl_new                    false
% 3.27/0.98  --res_prop_simpl_given                  true
% 3.27/0.98  --res_passive_queue_type                priority_queues
% 3.27/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.98  --res_passive_queues_freq               [15;5]
% 3.27/0.98  --res_forward_subs                      full
% 3.27/0.98  --res_backward_subs                     full
% 3.27/0.98  --res_forward_subs_resolution           true
% 3.27/0.98  --res_backward_subs_resolution          true
% 3.27/0.98  --res_orphan_elimination                true
% 3.27/0.98  --res_time_limit                        2.
% 3.27/0.98  --res_out_proof                         true
% 3.27/0.98  
% 3.27/0.98  ------ Superposition Options
% 3.27/0.98  
% 3.27/0.98  --superposition_flag                    true
% 3.27/0.98  --sup_passive_queue_type                priority_queues
% 3.27/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.98  --demod_completeness_check              fast
% 3.27/0.98  --demod_use_ground                      true
% 3.27/0.98  --sup_to_prop_solver                    passive
% 3.27/0.98  --sup_prop_simpl_new                    true
% 3.27/0.98  --sup_prop_simpl_given                  true
% 3.27/0.98  --sup_fun_splitting                     false
% 3.27/0.98  --sup_smt_interval                      50000
% 3.27/0.98  
% 3.27/0.98  ------ Superposition Simplification Setup
% 3.27/0.98  
% 3.27/0.98  --sup_indices_passive                   []
% 3.27/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.98  --sup_full_bw                           [BwDemod]
% 3.27/0.98  --sup_immed_triv                        [TrivRules]
% 3.27/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.98  --sup_immed_bw_main                     []
% 3.27/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.98  
% 3.27/0.98  ------ Combination Options
% 3.27/0.98  
% 3.27/0.98  --comb_res_mult                         3
% 3.27/0.98  --comb_sup_mult                         2
% 3.27/0.98  --comb_inst_mult                        10
% 3.27/0.98  
% 3.27/0.98  ------ Debug Options
% 3.27/0.98  
% 3.27/0.98  --dbg_backtrace                         false
% 3.27/0.98  --dbg_dump_prop_clauses                 false
% 3.27/0.98  --dbg_dump_prop_clauses_file            -
% 3.27/0.98  --dbg_out_stat                          false
% 3.27/0.98  ------ Parsing...
% 3.27/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/0.98  
% 3.27/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.27/0.98  
% 3.27/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/0.98  
% 3.27/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/0.98  ------ Proving...
% 3.27/0.98  ------ Problem Properties 
% 3.27/0.98  
% 3.27/0.98  
% 3.27/0.98  clauses                                 29
% 3.27/0.98  conjectures                             5
% 3.27/0.98  EPR                                     2
% 3.27/0.98  Horn                                    25
% 3.27/0.98  unary                                   7
% 3.27/0.98  binary                                  10
% 3.27/0.98  lits                                    82
% 3.27/0.98  lits eq                                 22
% 3.27/0.98  fd_pure                                 0
% 3.27/0.98  fd_pseudo                               0
% 3.27/0.98  fd_cond                                 0
% 3.27/0.98  fd_pseudo_cond                          7
% 3.27/0.98  AC symbols                              0
% 3.27/0.98  
% 3.27/0.98  ------ Schedule dynamic 5 is on 
% 3.27/0.98  
% 3.27/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/0.98  
% 3.27/0.98  
% 3.27/0.98  ------ 
% 3.27/0.98  Current options:
% 3.27/0.98  ------ 
% 3.27/0.98  
% 3.27/0.98  ------ Input Options
% 3.27/0.98  
% 3.27/0.98  --out_options                           all
% 3.27/0.98  --tptp_safe_out                         true
% 3.27/0.98  --problem_path                          ""
% 3.27/0.98  --include_path                          ""
% 3.27/0.98  --clausifier                            res/vclausify_rel
% 3.27/0.98  --clausifier_options                    --mode clausify
% 3.27/0.98  --stdin                                 false
% 3.27/0.98  --stats_out                             all
% 3.27/0.98  
% 3.27/0.98  ------ General Options
% 3.27/0.98  
% 3.27/0.98  --fof                                   false
% 3.27/0.98  --time_out_real                         305.
% 3.27/0.98  --time_out_virtual                      -1.
% 3.27/0.98  --symbol_type_check                     false
% 3.27/0.98  --clausify_out                          false
% 3.27/0.98  --sig_cnt_out                           false
% 3.27/0.98  --trig_cnt_out                          false
% 3.27/0.98  --trig_cnt_out_tolerance                1.
% 3.27/0.98  --trig_cnt_out_sk_spl                   false
% 3.27/0.98  --abstr_cl_out                          false
% 3.27/0.98  
% 3.27/0.98  ------ Global Options
% 3.27/0.98  
% 3.27/0.98  --schedule                              default
% 3.27/0.98  --add_important_lit                     false
% 3.27/0.98  --prop_solver_per_cl                    1000
% 3.27/0.98  --min_unsat_core                        false
% 3.27/0.98  --soft_assumptions                      false
% 3.27/0.98  --soft_lemma_size                       3
% 3.27/0.98  --prop_impl_unit_size                   0
% 3.27/0.98  --prop_impl_unit                        []
% 3.27/0.98  --share_sel_clauses                     true
% 3.27/0.98  --reset_solvers                         false
% 3.27/0.98  --bc_imp_inh                            [conj_cone]
% 3.27/0.98  --conj_cone_tolerance                   3.
% 3.27/0.98  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     none
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       false
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ Proving...
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS status Theorem for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  fof(f3,axiom,(
% 3.27/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f8,plain,(
% 3.27/0.99    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.27/0.99    inference(ennf_transformation,[],[f3])).
% 3.27/0.99  
% 3.27/0.99  fof(f9,plain,(
% 3.27/0.99    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(flattening,[],[f8])).
% 3.27/0.99  
% 3.27/0.99  fof(f26,plain,(
% 3.27/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(nnf_transformation,[],[f9])).
% 3.27/0.99  
% 3.27/0.99  fof(f27,plain,(
% 3.27/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(flattening,[],[f26])).
% 3.27/0.99  
% 3.27/0.99  fof(f28,plain,(
% 3.27/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(rectify,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f29,plain,(
% 3.27/0.99    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1) & r2_hidden(sK7(X0,X1),X0)))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f30,plain,(
% 3.27/0.99    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1) & r2_hidden(sK7(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 3.27/0.99  
% 3.27/0.99  fof(f48,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK7(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f30])).
% 3.27/0.99  
% 3.27/0.99  fof(f66,plain,(
% 3.27/0.99    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK7(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(equality_resolution,[],[f48])).
% 3.27/0.99  
% 3.27/0.99  fof(f5,conjecture,(
% 3.27/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f6,negated_conjecture,(
% 3.27/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 3.27/0.99    inference(negated_conjecture,[],[f5])).
% 3.27/0.99  
% 3.27/0.99  fof(f12,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f6])).
% 3.27/0.99  
% 3.27/0.99  fof(f13,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.27/0.99    inference(flattening,[],[f12])).
% 3.27/0.99  
% 3.27/0.99  fof(f34,plain,(
% 3.27/0.99    ( ! [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK9)) != sK9 & k5_relat_1(X0,sK9) = X0 & k2_relat_1(X0) = k1_relat_1(sK9) & v1_funct_1(sK9) & v1_relat_1(sK9))) )),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f33,plain,(
% 3.27/0.99    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(sK8,X1) = sK8 & k2_relat_1(sK8) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK8) & v1_relat_1(sK8))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f35,plain,(
% 3.27/0.99    (k6_relat_1(k1_relat_1(sK9)) != sK9 & k5_relat_1(sK8,sK9) = sK8 & k2_relat_1(sK8) = k1_relat_1(sK9) & v1_funct_1(sK9) & v1_relat_1(sK9)) & v1_funct_1(sK8) & v1_relat_1(sK8)),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f13,f34,f33])).
% 3.27/0.99  
% 3.27/0.99  fof(f56,plain,(
% 3.27/0.99    v1_funct_1(sK9)),
% 3.27/0.99    inference(cnf_transformation,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f55,plain,(
% 3.27/0.99    v1_relat_1(sK9)),
% 3.27/0.99    inference(cnf_transformation,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f59,plain,(
% 3.27/0.99    k6_relat_1(k1_relat_1(sK9)) != sK9),
% 3.27/0.99    inference(cnf_transformation,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f57,plain,(
% 3.27/0.99    k2_relat_1(sK8) = k1_relat_1(sK9)),
% 3.27/0.99    inference(cnf_transformation,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f1,axiom,(
% 3.27/0.99    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f14,plain,(
% 3.27/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.27/0.99    inference(nnf_transformation,[],[f1])).
% 3.27/0.99  
% 3.27/0.99  fof(f15,plain,(
% 3.27/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.27/0.99    inference(rectify,[],[f14])).
% 3.27/0.99  
% 3.27/0.99  fof(f18,plain,(
% 3.27/0.99    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f17,plain,(
% 3.27/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0))) )),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f16,plain,(
% 3.27/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f19,plain,(
% 3.27/0.99    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).
% 3.27/0.99  
% 3.27/0.99  fof(f36,plain,(
% 3.27/0.99    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.27/0.99    inference(cnf_transformation,[],[f19])).
% 3.27/0.99  
% 3.27/0.99  fof(f61,plain,(
% 3.27/0.99    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.27/0.99    inference(equality_resolution,[],[f36])).
% 3.27/0.99  
% 3.27/0.99  fof(f58,plain,(
% 3.27/0.99    k5_relat_1(sK8,sK9) = sK8),
% 3.27/0.99    inference(cnf_transformation,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f4,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f10,plain,(
% 3.27/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.27/0.99    inference(ennf_transformation,[],[f4])).
% 3.27/0.99  
% 3.27/0.99  fof(f11,plain,(
% 3.27/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.27/0.99    inference(flattening,[],[f10])).
% 3.27/0.99  
% 3.27/0.99  fof(f31,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.27/0.99    inference(nnf_transformation,[],[f11])).
% 3.27/0.99  
% 3.27/0.99  fof(f32,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.27/0.99    inference(flattening,[],[f31])).
% 3.27/0.99  
% 3.27/0.99  fof(f52,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f32])).
% 3.27/0.99  
% 3.27/0.99  fof(f69,plain,(
% 3.27/0.99    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.27/0.99    inference(equality_resolution,[],[f52])).
% 3.27/0.99  
% 3.27/0.99  fof(f2,axiom,(
% 3.27/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f7,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(ennf_transformation,[],[f2])).
% 3.27/0.99  
% 3.27/0.99  fof(f20,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(nnf_transformation,[],[f7])).
% 3.27/0.99  
% 3.27/0.99  fof(f21,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(rectify,[],[f20])).
% 3.27/0.99  
% 3.27/0.99  fof(f24,plain,(
% 3.27/0.99    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f23,plain,(
% 3.27/0.99    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK5(X0,X1,X2)),X0)))) )),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f22,plain,(
% 3.27/0.99    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f25,plain,(
% 3.27/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f21,f24,f23,f22])).
% 3.27/0.99  
% 3.27/0.99  fof(f42,plain,(
% 3.27/0.99    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f25])).
% 3.27/0.99  
% 3.27/0.99  fof(f62,plain,(
% 3.27/0.99    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(equality_resolution,[],[f42])).
% 3.27/0.99  
% 3.27/0.99  fof(f53,plain,(
% 3.27/0.99    v1_relat_1(sK8)),
% 3.27/0.99    inference(cnf_transformation,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f37,plain,(
% 3.27/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.27/0.99    inference(cnf_transformation,[],[f19])).
% 3.27/0.99  
% 3.27/0.99  fof(f60,plain,(
% 3.27/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.27/0.99    inference(equality_resolution,[],[f37])).
% 3.27/0.99  
% 3.27/0.99  fof(f51,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f32])).
% 3.27/0.99  
% 3.27/0.99  fof(f54,plain,(
% 3.27/0.99    v1_funct_1(sK8)),
% 3.27/0.99    inference(cnf_transformation,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f49,plain,(
% 3.27/0.99    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f30])).
% 3.27/0.99  
% 3.27/0.99  fof(f65,plain,(
% 3.27/0.99    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK7(k1_relat_1(X1),X1)) != sK7(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(equality_resolution,[],[f49])).
% 3.27/0.99  
% 3.27/0.99  cnf(c_11,plain,
% 3.27/0.99      ( r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0))
% 3.27/0.99      | ~ v1_funct_1(X0)
% 3.27/0.99      | ~ v1_relat_1(X0)
% 3.27/0.99      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_20,negated_conjecture,
% 3.27/0.99      ( v1_funct_1(sK9) ),
% 3.27/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_313,plain,
% 3.27/0.99      ( r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0))
% 3.27/0.99      | ~ v1_relat_1(X0)
% 3.27/0.99      | k6_relat_1(k1_relat_1(X0)) = X0
% 3.27/0.99      | sK9 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_314,plain,
% 3.27/0.99      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
% 3.27/0.99      | ~ v1_relat_1(sK9)
% 3.27/0.99      | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_313]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_21,negated_conjecture,
% 3.27/0.99      ( v1_relat_1(sK9) ),
% 3.27/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_17,negated_conjecture,
% 3.27/0.99      ( k6_relat_1(k1_relat_1(sK9)) != sK9 ),
% 3.27/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_44,plain,
% 3.27/0.99      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
% 3.27/0.99      | ~ v1_funct_1(sK9)
% 3.27/0.99      | ~ v1_relat_1(sK9)
% 3.27/0.99      | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_316,plain,
% 3.27/0.99      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_314,c_21,c_20,c_17,c_44]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_909,plain,
% 3.27/0.99      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_19,negated_conjecture,
% 3.27/0.99      ( k2_relat_1(sK8) = k1_relat_1(sK9) ),
% 3.27/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_937,plain,
% 3.27/0.99      ( r2_hidden(sK7(k2_relat_1(sK8),sK9),k2_relat_1(sK8)) = iProver_top ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_909,c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.27/0.99      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_922,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_18,negated_conjecture,
% 3.27/0.99      ( k5_relat_1(sK8,sK9) = sK8 ),
% 3.27/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_14,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.27/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.27/0.99      | ~ v1_funct_1(X1)
% 3.27/0.99      | ~ v1_relat_1(X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_259,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.27/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.27/0.99      | ~ v1_relat_1(X1)
% 3.27/0.99      | sK9 != X1 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_260,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 3.27/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
% 3.27/0.99      | ~ v1_relat_1(sK9) ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_259]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_264,plain,
% 3.27/0.99      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
% 3.27/0.99      | ~ r2_hidden(X0,k1_relat_1(sK9)) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_260,c_21]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_265,plain,
% 3.27/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 3.27/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_264]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_912,plain,
% 3.27/0.99      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_972,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_912,c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7,plain,
% 3.27/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.27/0.99      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 3.27/0.99      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 3.27/0.99      | ~ v1_relat_1(X2)
% 3.27/0.99      | ~ v1_relat_1(X4)
% 3.27/0.99      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_918,plain,
% 3.27/0.99      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
% 3.27/0.99      | v1_relat_1(X2) != iProver_top
% 3.27/0.99      | v1_relat_1(X4) != iProver_top
% 3.27/0.99      | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2254,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
% 3.27/0.99      | v1_relat_1(X2) != iProver_top
% 3.27/0.99      | v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top
% 3.27/0.99      | v1_relat_1(sK9) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_972,c_918]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_26,plain,
% 3.27/0.99      ( v1_relat_1(sK9) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2686,plain,
% 3.27/0.99      ( v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top
% 3.27/0.99      | v1_relat_1(X2) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 3.27/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_2254,c_26]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2687,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
% 3.27/0.99      | v1_relat_1(X2) != iProver_top
% 3.27/0.99      | v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_2686]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2695,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
% 3.27/0.99      | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
% 3.27/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_18,c_2687]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2735,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
% 3.27/0.99      | v1_relat_1(sK8) != iProver_top ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_2695,c_18]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_23,negated_conjecture,
% 3.27/0.99      ( v1_relat_1(sK8) ),
% 3.27/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_24,plain,
% 3.27/0.99      ( v1_relat_1(sK8) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2907,plain,
% 3.27/0.99      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
% 3.27/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_2735,c_24]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2908,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_2907]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_923,plain,
% 3.27/0.99      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2916,plain,
% 3.27/0.99      ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.27/0.99      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X1)),sK8) = iProver_top ),
% 3.27/0.99      inference(forward_subsumption_resolution,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_2908,c_923]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_15,plain,
% 3.27/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.27/0.99      | ~ v1_funct_1(X2)
% 3.27/0.99      | ~ v1_relat_1(X2)
% 3.27/0.99      | k1_funct_1(X2,X0) = X1 ),
% 3.27/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_22,negated_conjecture,
% 3.27/0.99      ( v1_funct_1(sK8) ),
% 3.27/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_437,plain,
% 3.27/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.27/0.99      | ~ v1_relat_1(X2)
% 3.27/0.99      | k1_funct_1(X2,X0) = X1
% 3.27/0.99      | sK8 != X2 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_438,plain,
% 3.27/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.27/0.99      | ~ v1_relat_1(sK8)
% 3.27/0.99      | k1_funct_1(sK8,X0) = X1 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_442,plain,
% 3.27/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK8) | k1_funct_1(sK8,X0) = X1 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_438,c_23]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_902,plain,
% 3.27/0.99      ( k1_funct_1(sK8,X0) = X1
% 3.27/0.99      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2923,plain,
% 3.27/0.99      ( k1_funct_1(sK9,X0) = k1_funct_1(sK8,X1)
% 3.27/0.99      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_2916,c_902]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5551,plain,
% 3.27/0.99      ( k1_funct_1(sK8,sK2(sK8,X0)) = k1_funct_1(sK9,X0)
% 3.27/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_922,c_2923]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7076,plain,
% 3.27/0.99      ( k1_funct_1(sK8,sK2(sK8,sK7(k2_relat_1(sK8),sK9))) = k1_funct_1(sK9,sK7(k2_relat_1(sK8),sK9)) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_937,c_5551]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1417,plain,
% 3.27/0.99      ( k1_funct_1(sK8,sK2(sK8,X0)) = X0
% 3.27/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_922,c_902]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3030,plain,
% 3.27/0.99      ( k1_funct_1(sK8,sK2(sK8,sK7(k2_relat_1(sK8),sK9))) = sK7(k2_relat_1(sK8),sK9) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_937,c_1417]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7197,plain,
% 3.27/0.99      ( k1_funct_1(sK9,sK7(k2_relat_1(sK8),sK9)) = sK7(k2_relat_1(sK8),sK9) ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_7076,c_3030]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_10,plain,
% 3.27/0.99      ( ~ v1_funct_1(X0)
% 3.27/0.99      | ~ v1_relat_1(X0)
% 3.27/0.99      | k1_funct_1(X0,sK7(k1_relat_1(X0),X0)) != sK7(k1_relat_1(X0),X0)
% 3.27/0.99      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_324,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0)
% 3.27/0.99      | k1_funct_1(X0,sK7(k1_relat_1(X0),X0)) != sK7(k1_relat_1(X0),X0)
% 3.27/0.99      | k6_relat_1(k1_relat_1(X0)) = X0
% 3.27/0.99      | sK9 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_325,plain,
% 3.27/0.99      ( ~ v1_relat_1(sK9)
% 3.27/0.99      | k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) != sK7(k1_relat_1(sK9),sK9)
% 3.27/0.99      | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_47,plain,
% 3.27/0.99      ( ~ v1_funct_1(sK9)
% 3.27/0.99      | ~ v1_relat_1(sK9)
% 3.27/0.99      | k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) != sK7(k1_relat_1(sK9),sK9)
% 3.27/0.99      | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_327,plain,
% 3.27/0.99      ( k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) != sK7(k1_relat_1(sK9),sK9) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_325,c_21,c_20,c_17,c_47]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_940,plain,
% 3.27/0.99      ( k1_funct_1(sK9,sK7(k2_relat_1(sK8),sK9)) != sK7(k2_relat_1(sK8),sK9) ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_327,c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(contradiction,plain,
% 3.27/0.99      ( $false ),
% 3.27/0.99      inference(minisat,[status(thm)],[c_7197,c_940]) ).
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  ------                               Statistics
% 3.27/0.99  
% 3.27/0.99  ------ General
% 3.27/0.99  
% 3.27/0.99  abstr_ref_over_cycles:                  0
% 3.27/0.99  abstr_ref_under_cycles:                 0
% 3.27/0.99  gc_basic_clause_elim:                   0
% 3.27/0.99  forced_gc_time:                         0
% 3.27/0.99  parsing_time:                           0.011
% 3.27/0.99  unif_index_cands_time:                  0.
% 3.27/0.99  unif_index_add_time:                    0.
% 3.27/0.99  orderings_time:                         0.
% 3.27/0.99  out_proof_time:                         0.008
% 3.27/0.99  total_time:                             0.258
% 3.27/0.99  num_of_symbols:                         50
% 3.27/0.99  num_of_terms:                           7600
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing
% 3.27/0.99  
% 3.27/0.99  num_of_splits:                          0
% 3.27/0.99  num_of_split_atoms:                     0
% 3.27/0.99  num_of_reused_defs:                     0
% 3.27/0.99  num_eq_ax_congr_red:                    39
% 3.27/0.99  num_of_sem_filtered_clauses:            1
% 3.27/0.99  num_of_subtypes:                        0
% 3.27/0.99  monotx_restored_types:                  0
% 3.27/0.99  sat_num_of_epr_types:                   0
% 3.27/0.99  sat_num_of_non_cyclic_types:            0
% 3.27/0.99  sat_guarded_non_collapsed_types:        0
% 3.27/0.99  num_pure_diseq_elim:                    0
% 3.27/0.99  simp_replaced_by:                       0
% 3.27/0.99  res_preprocessed:                       105
% 3.27/0.99  prep_upred:                             0
% 3.27/0.99  prep_unflattend:                        10
% 3.27/0.99  smt_new_axioms:                         0
% 3.27/0.99  pred_elim_cands:                        3
% 3.27/0.99  pred_elim:                              1
% 3.27/0.99  pred_elim_cl:                           -5
% 3.27/0.99  pred_elim_cycles:                       2
% 3.27/0.99  merged_defs:                            0
% 3.27/0.99  merged_defs_ncl:                        0
% 3.27/0.99  bin_hyper_res:                          0
% 3.27/0.99  prep_cycles:                            3
% 3.27/0.99  pred_elim_time:                         0.004
% 3.27/0.99  splitting_time:                         0.
% 3.27/0.99  sem_filter_time:                        0.
% 3.27/0.99  monotx_time:                            0.001
% 3.27/0.99  subtype_inf_time:                       0.
% 3.27/0.99  
% 3.27/0.99  ------ Problem properties
% 3.27/0.99  
% 3.27/0.99  clauses:                                29
% 3.27/0.99  conjectures:                            5
% 3.27/0.99  epr:                                    2
% 3.27/0.99  horn:                                   25
% 3.27/0.99  ground:                                 9
% 3.27/0.99  unary:                                  7
% 3.27/0.99  binary:                                 10
% 3.27/0.99  lits:                                   82
% 3.27/0.99  lits_eq:                                22
% 3.27/0.99  fd_pure:                                0
% 3.27/0.99  fd_pseudo:                              0
% 3.27/0.99  fd_cond:                                0
% 3.27/0.99  fd_pseudo_cond:                         7
% 3.27/0.99  ac_symbols:                             0
% 3.27/0.99  
% 3.27/0.99  ------ Propositional Solver
% 3.27/0.99  
% 3.27/0.99  prop_solver_calls:                      23
% 3.27/0.99  prop_fast_solver_calls:                 895
% 3.27/0.99  smt_solver_calls:                       0
% 3.27/0.99  smt_fast_solver_calls:                  0
% 3.27/0.99  prop_num_of_clauses:                    2546
% 3.27/0.99  prop_preprocess_simplified:             5215
% 3.27/0.99  prop_fo_subsumed:                       22
% 3.27/0.99  prop_solver_time:                       0.
% 3.27/0.99  smt_solver_time:                        0.
% 3.27/0.99  smt_fast_solver_time:                   0.
% 3.27/0.99  prop_fast_solver_time:                  0.
% 3.27/0.99  prop_unsat_core_time:                   0.
% 3.27/0.99  
% 3.27/0.99  ------ QBF
% 3.27/0.99  
% 3.27/0.99  qbf_q_res:                              0
% 3.27/0.99  qbf_num_tautologies:                    0
% 3.27/0.99  qbf_prep_cycles:                        0
% 3.27/0.99  
% 3.27/0.99  ------ BMC1
% 3.27/0.99  
% 3.27/0.99  bmc1_current_bound:                     -1
% 3.27/0.99  bmc1_last_solved_bound:                 -1
% 3.27/0.99  bmc1_unsat_core_size:                   -1
% 3.27/0.99  bmc1_unsat_core_parents_size:           -1
% 3.27/0.99  bmc1_merge_next_fun:                    0
% 3.27/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation
% 3.27/0.99  
% 3.27/0.99  inst_num_of_clauses:                    576
% 3.27/0.99  inst_num_in_passive:                    64
% 3.27/0.99  inst_num_in_active:                     272
% 3.27/0.99  inst_num_in_unprocessed:                240
% 3.27/0.99  inst_num_of_loops:                      310
% 3.27/0.99  inst_num_of_learning_restarts:          0
% 3.27/0.99  inst_num_moves_active_passive:          35
% 3.27/0.99  inst_lit_activity:                      0
% 3.27/0.99  inst_lit_activity_moves:                0
% 3.27/0.99  inst_num_tautologies:                   0
% 3.27/0.99  inst_num_prop_implied:                  0
% 3.27/0.99  inst_num_existing_simplified:           0
% 3.27/0.99  inst_num_eq_res_simplified:             0
% 3.27/0.99  inst_num_child_elim:                    0
% 3.27/0.99  inst_num_of_dismatching_blockings:      126
% 3.27/0.99  inst_num_of_non_proper_insts:           481
% 3.27/0.99  inst_num_of_duplicates:                 0
% 3.27/0.99  inst_inst_num_from_inst_to_res:         0
% 3.27/0.99  inst_dismatching_checking_time:         0.
% 3.27/0.99  
% 3.27/0.99  ------ Resolution
% 3.27/0.99  
% 3.27/0.99  res_num_of_clauses:                     0
% 3.27/0.99  res_num_in_passive:                     0
% 3.27/0.99  res_num_in_active:                      0
% 3.27/0.99  res_num_of_loops:                       108
% 3.27/0.99  res_forward_subset_subsumed:            79
% 3.27/0.99  res_backward_subset_subsumed:           0
% 3.27/0.99  res_forward_subsumed:                   0
% 3.27/0.99  res_backward_subsumed:                  0
% 3.27/0.99  res_forward_subsumption_resolution:     0
% 3.27/0.99  res_backward_subsumption_resolution:    0
% 3.27/0.99  res_clause_to_clause_subsumption:       606
% 3.27/0.99  res_orphan_elimination:                 0
% 3.27/0.99  res_tautology_del:                      78
% 3.27/0.99  res_num_eq_res_simplified:              0
% 3.27/0.99  res_num_sel_changes:                    0
% 3.27/0.99  res_moves_from_active_to_pass:          0
% 3.27/0.99  
% 3.27/0.99  ------ Superposition
% 3.27/0.99  
% 3.27/0.99  sup_time_total:                         0.
% 3.27/0.99  sup_time_generating:                    0.
% 3.27/0.99  sup_time_sim_full:                      0.
% 3.27/0.99  sup_time_sim_immed:                     0.
% 3.27/0.99  
% 3.27/0.99  sup_num_of_clauses:                     301
% 3.27/0.99  sup_num_in_active:                      62
% 3.27/0.99  sup_num_in_passive:                     239
% 3.27/0.99  sup_num_of_loops:                       61
% 3.27/0.99  sup_fw_superposition:                   175
% 3.27/0.99  sup_bw_superposition:                   125
% 3.27/0.99  sup_immediate_simplified:               9
% 3.27/0.99  sup_given_eliminated:                   0
% 3.27/0.99  comparisons_done:                       0
% 3.27/0.99  comparisons_avoided:                    4
% 3.27/0.99  
% 3.27/0.99  ------ Simplifications
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  sim_fw_subset_subsumed:                 5
% 3.27/0.99  sim_bw_subset_subsumed:                 0
% 3.27/0.99  sim_fw_subsumed:                        2
% 3.27/0.99  sim_bw_subsumed:                        0
% 3.27/0.99  sim_fw_subsumption_res:                 1
% 3.27/0.99  sim_bw_subsumption_res:                 0
% 3.27/0.99  sim_tautology_del:                      5
% 3.27/0.99  sim_eq_tautology_del:                   13
% 3.27/0.99  sim_eq_res_simp:                        0
% 3.27/0.99  sim_fw_demodulated:                     0
% 3.27/0.99  sim_bw_demodulated:                     0
% 3.27/0.99  sim_light_normalised:                   7
% 3.27/0.99  sim_joinable_taut:                      0
% 3.27/0.99  sim_joinable_simp:                      0
% 3.27/0.99  sim_ac_normalised:                      0
% 3.27/0.99  sim_smt_subsumption:                    0
% 3.27/0.99  
%------------------------------------------------------------------------------

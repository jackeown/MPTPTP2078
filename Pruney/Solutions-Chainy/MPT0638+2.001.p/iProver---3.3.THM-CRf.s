%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:12 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 598 expanded)
%              Number of clauses        :   78 ( 153 expanded)
%              Number of leaves         :   17 ( 159 expanded)
%              Depth                    :   22
%              Number of atoms          :  623 (3764 expanded)
%              Number of equality atoms :  264 (1696 expanded)
%              Maximal formula depth    :   16 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK7(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK7(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k1_relat_1(X1) = k2_relat_1(X0) )
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
                & k1_relat_1(X1) = k2_relat_1(X0) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k1_relat_1(X1) = k2_relat_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k6_relat_1(k1_relat_1(sK9)) != sK9
        & k5_relat_1(X0,sK9) = X0
        & k1_relat_1(sK9) = k2_relat_1(X0)
        & v1_funct_1(sK9)
        & v1_relat_1(sK9) ) ) ),
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
          & k5_relat_1(sK8,X1) = sK8
          & k1_relat_1(X1) = k2_relat_1(sK8)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k6_relat_1(k1_relat_1(sK9)) != sK9
    & k5_relat_1(sK8,sK9) = sK8
    & k1_relat_1(sK9) = k2_relat_1(sK8)
    & v1_funct_1(sK9)
    & v1_relat_1(sK9)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f15,f35,f34])).

fof(f60,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    k6_relat_1(k1_relat_1(sK9)) != sK9 ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f58,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    k1_relat_1(sK9) = k2_relat_1(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f2])).

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

fof(f22,plain,(
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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f62,plain,(
    k5_relat_1(sK8,sK9) = sK8 ),
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
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
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
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f20,f19,f18])).

fof(f39,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK7(k1_relat_1(X1),X1)) != sK7(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f56])).

cnf(c_17,plain,
    ( r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_266,plain,
    ( r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_267,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
    | ~ v1_relat_1(sK9)
    | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( k6_relat_1(k1_relat_1(sK9)) != sK9 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_38,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_269,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_267,c_24,c_23,c_20,c_38])).

cnf(c_1364,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK6(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_547,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK6(X1,X0)) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_548,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,sK6(sK8,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_552,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK8))
    | k1_funct_1(sK8,sK6(sK8,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_26])).

cnf(c_1350,plain,
    ( k1_funct_1(sK8,sK6(sK8,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_22,negated_conjecture,
    ( k1_relat_1(sK9) = k2_relat_1(sK8) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1395,plain,
    ( k1_funct_1(sK8,sK6(sK8,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1350,c_22])).

cnf(c_1957,plain,
    ( k1_funct_1(sK8,sK6(sK8,sK7(k1_relat_1(sK9),sK9))) = sK7(k1_relat_1(sK9),sK9) ),
    inference(superposition,[status(thm)],[c_1364,c_1395])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_607,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_608,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_612,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_26])).

cnf(c_613,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
    inference(renaming,[status(thm)],[c_612])).

cnf(c_1347,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_2306,plain,
    ( r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),sK7(k1_relat_1(sK9),sK9)),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1347])).

cnf(c_29,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_37,plain,
    ( k6_relat_1(k1_relat_1(X0)) = X0
    | r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_39,plain,
    ( k6_relat_1(k1_relat_1(sK9)) = sK9
    | r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_817,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1904,plain,
    ( k2_relat_1(sK8) = k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_2312,plain,
    ( sK7(k1_relat_1(sK9),sK9) = sK7(k1_relat_1(sK9),sK9) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_818,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1822,plain,
    ( X0 != X1
    | X0 = k1_relat_1(sK9)
    | k1_relat_1(sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_2330,plain,
    ( X0 != k2_relat_1(sK8)
    | X0 = k1_relat_1(sK9)
    | k1_relat_1(sK9) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_1822])).

cnf(c_2519,plain,
    ( k2_relat_1(sK8) != k2_relat_1(sK8)
    | k2_relat_1(sK8) = k1_relat_1(sK9)
    | k1_relat_1(sK9) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2330])).

cnf(c_821,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1722,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
    | X0 != sK7(k1_relat_1(sK9),sK9)
    | X1 != k1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_1839,plain,
    ( r2_hidden(X0,k2_relat_1(sK8))
    | ~ r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
    | X0 != sK7(k1_relat_1(sK9),sK9)
    | k2_relat_1(sK8) != k1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_4626,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k2_relat_1(sK8))
    | ~ r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
    | sK7(k1_relat_1(sK9),sK9) != sK7(k1_relat_1(sK9),sK9)
    | k2_relat_1(sK8) != k1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_4639,plain,
    ( sK7(k1_relat_1(sK9),sK9) != sK7(k1_relat_1(sK9),sK9)
    | k2_relat_1(sK8) != k1_relat_1(sK9)
    | r2_hidden(sK7(k1_relat_1(sK9),sK9),k2_relat_1(sK8)) = iProver_top
    | r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4626])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK6(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_529,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK6(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_530,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK8))
    | r2_hidden(sK6(sK8,X0),k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_534,plain,
    ( r2_hidden(sK6(sK8,X0),k1_relat_1(sK8))
    | ~ r2_hidden(X0,k2_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_26])).

cnf(c_535,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK8))
    | r2_hidden(sK6(sK8,X0),k1_relat_1(sK8)) ),
    inference(renaming,[status(thm)],[c_534])).

cnf(c_7305,plain,
    ( ~ r2_hidden(sK7(k1_relat_1(sK9),sK9),k2_relat_1(sK8))
    | r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_7306,plain,
    ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k2_relat_1(sK8)) != iProver_top
    | r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7305])).

cnf(c_17055,plain,
    ( r2_hidden(k4_tarski(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),sK7(k1_relat_1(sK9),sK9)),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2306,c_29,c_30,c_22,c_20,c_39,c_1904,c_2312,c_2519,c_4639,c_7306])).

cnf(c_21,negated_conjecture,
    ( k5_relat_1(sK8,sK9) = sK8 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_472,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_473,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_477,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
    | ~ r2_hidden(X0,k1_relat_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_24])).

cnf(c_478,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) ),
    inference(renaming,[status(thm)],[c_477])).

cnf(c_1354,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_3,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1369,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top
    | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2617,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1369])).

cnf(c_22633,plain,
    ( v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2617,c_29])).

cnf(c_22634,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22633])).

cnf(c_22645,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
    | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_22634])).

cnf(c_22694,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22645,c_21])).

cnf(c_27,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22763,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22694,c_27])).

cnf(c_22764,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_22763])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_625,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_626,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_630,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | k1_funct_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_26])).

cnf(c_631,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(renaming,[status(thm)],[c_630])).

cnf(c_1346,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_22776,plain,
    ( k1_funct_1(sK8,X0) = k1_funct_1(sK9,X1)
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_22764,c_1346])).

cnf(c_23091,plain,
    ( k1_funct_1(sK8,sK6(sK8,sK7(k1_relat_1(sK9),sK9))) = k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9))
    | r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) != iProver_top
    | r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17055,c_22776])).

cnf(c_23106,plain,
    ( k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) = sK7(k1_relat_1(sK9),sK9)
    | r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) != iProver_top
    | r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23091,c_1957])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK7(k1_relat_1(X0),X0)) != sK7(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) != sK7(k1_relat_1(sK9),sK9)
    | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23106,c_7306,c_4639,c_2519,c_2312,c_1904,c_41,c_39,c_20,c_22,c_30,c_23,c_29,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.61/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.48  
% 7.61/1.48  ------  iProver source info
% 7.61/1.48  
% 7.61/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.48  git: non_committed_changes: false
% 7.61/1.48  git: last_make_outside_of_git: false
% 7.61/1.48  
% 7.61/1.48  ------ 
% 7.61/1.48  
% 7.61/1.48  ------ Input Options
% 7.61/1.48  
% 7.61/1.48  --out_options                           all
% 7.61/1.48  --tptp_safe_out                         true
% 7.61/1.48  --problem_path                          ""
% 7.61/1.48  --include_path                          ""
% 7.61/1.48  --clausifier                            res/vclausify_rel
% 7.61/1.48  --clausifier_options                    --mode clausify
% 7.61/1.48  --stdin                                 false
% 7.61/1.48  --stats_out                             all
% 7.61/1.48  
% 7.61/1.48  ------ General Options
% 7.61/1.48  
% 7.61/1.48  --fof                                   false
% 7.61/1.48  --time_out_real                         305.
% 7.61/1.48  --time_out_virtual                      -1.
% 7.61/1.48  --symbol_type_check                     false
% 7.61/1.48  --clausify_out                          false
% 7.61/1.48  --sig_cnt_out                           false
% 7.61/1.48  --trig_cnt_out                          false
% 7.61/1.48  --trig_cnt_out_tolerance                1.
% 7.61/1.48  --trig_cnt_out_sk_spl                   false
% 7.61/1.48  --abstr_cl_out                          false
% 7.61/1.48  
% 7.61/1.48  ------ Global Options
% 7.61/1.48  
% 7.61/1.48  --schedule                              default
% 7.61/1.48  --add_important_lit                     false
% 7.61/1.48  --prop_solver_per_cl                    1000
% 7.61/1.48  --min_unsat_core                        false
% 7.61/1.48  --soft_assumptions                      false
% 7.61/1.48  --soft_lemma_size                       3
% 7.61/1.48  --prop_impl_unit_size                   0
% 7.61/1.48  --prop_impl_unit                        []
% 7.61/1.48  --share_sel_clauses                     true
% 7.61/1.48  --reset_solvers                         false
% 7.61/1.48  --bc_imp_inh                            [conj_cone]
% 7.61/1.48  --conj_cone_tolerance                   3.
% 7.61/1.48  --extra_neg_conj                        none
% 7.61/1.48  --large_theory_mode                     true
% 7.61/1.48  --prolific_symb_bound                   200
% 7.61/1.48  --lt_threshold                          2000
% 7.61/1.48  --clause_weak_htbl                      true
% 7.61/1.48  --gc_record_bc_elim                     false
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing Options
% 7.61/1.48  
% 7.61/1.48  --preprocessing_flag                    true
% 7.61/1.48  --time_out_prep_mult                    0.1
% 7.61/1.48  --splitting_mode                        input
% 7.61/1.48  --splitting_grd                         true
% 7.61/1.48  --splitting_cvd                         false
% 7.61/1.48  --splitting_cvd_svl                     false
% 7.61/1.48  --splitting_nvd                         32
% 7.61/1.48  --sub_typing                            true
% 7.61/1.48  --prep_gs_sim                           true
% 7.61/1.48  --prep_unflatten                        true
% 7.61/1.48  --prep_res_sim                          true
% 7.61/1.48  --prep_upred                            true
% 7.61/1.48  --prep_sem_filter                       exhaustive
% 7.61/1.48  --prep_sem_filter_out                   false
% 7.61/1.48  --pred_elim                             true
% 7.61/1.48  --res_sim_input                         true
% 7.61/1.48  --eq_ax_congr_red                       true
% 7.61/1.48  --pure_diseq_elim                       true
% 7.61/1.48  --brand_transform                       false
% 7.61/1.48  --non_eq_to_eq                          false
% 7.61/1.48  --prep_def_merge                        true
% 7.61/1.48  --prep_def_merge_prop_impl              false
% 7.61/1.48  --prep_def_merge_mbd                    true
% 7.61/1.48  --prep_def_merge_tr_red                 false
% 7.61/1.48  --prep_def_merge_tr_cl                  false
% 7.61/1.48  --smt_preprocessing                     true
% 7.61/1.48  --smt_ac_axioms                         fast
% 7.61/1.48  --preprocessed_out                      false
% 7.61/1.48  --preprocessed_stats                    false
% 7.61/1.48  
% 7.61/1.48  ------ Abstraction refinement Options
% 7.61/1.48  
% 7.61/1.48  --abstr_ref                             []
% 7.61/1.48  --abstr_ref_prep                        false
% 7.61/1.48  --abstr_ref_until_sat                   false
% 7.61/1.48  --abstr_ref_sig_restrict                funpre
% 7.61/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.61/1.48  --abstr_ref_under                       []
% 7.61/1.48  
% 7.61/1.48  ------ SAT Options
% 7.61/1.48  
% 7.61/1.48  --sat_mode                              false
% 7.61/1.48  --sat_fm_restart_options                ""
% 7.61/1.48  --sat_gr_def                            false
% 7.61/1.48  --sat_epr_types                         true
% 7.61/1.48  --sat_non_cyclic_types                  false
% 7.61/1.48  --sat_finite_models                     false
% 7.61/1.48  --sat_fm_lemmas                         false
% 7.61/1.48  --sat_fm_prep                           false
% 7.61/1.48  --sat_fm_uc_incr                        true
% 7.61/1.48  --sat_out_model                         small
% 7.61/1.48  --sat_out_clauses                       false
% 7.61/1.48  
% 7.61/1.48  ------ QBF Options
% 7.61/1.48  
% 7.61/1.48  --qbf_mode                              false
% 7.61/1.48  --qbf_elim_univ                         false
% 7.61/1.48  --qbf_dom_inst                          none
% 7.61/1.48  --qbf_dom_pre_inst                      false
% 7.61/1.48  --qbf_sk_in                             false
% 7.61/1.48  --qbf_pred_elim                         true
% 7.61/1.48  --qbf_split                             512
% 7.61/1.48  
% 7.61/1.48  ------ BMC1 Options
% 7.61/1.48  
% 7.61/1.48  --bmc1_incremental                      false
% 7.61/1.48  --bmc1_axioms                           reachable_all
% 7.61/1.48  --bmc1_min_bound                        0
% 7.61/1.48  --bmc1_max_bound                        -1
% 7.61/1.48  --bmc1_max_bound_default                -1
% 7.61/1.48  --bmc1_symbol_reachability              true
% 7.61/1.48  --bmc1_property_lemmas                  false
% 7.61/1.48  --bmc1_k_induction                      false
% 7.61/1.48  --bmc1_non_equiv_states                 false
% 7.61/1.48  --bmc1_deadlock                         false
% 7.61/1.48  --bmc1_ucm                              false
% 7.61/1.48  --bmc1_add_unsat_core                   none
% 7.61/1.48  --bmc1_unsat_core_children              false
% 7.61/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.61/1.48  --bmc1_out_stat                         full
% 7.61/1.48  --bmc1_ground_init                      false
% 7.61/1.48  --bmc1_pre_inst_next_state              false
% 7.61/1.48  --bmc1_pre_inst_state                   false
% 7.61/1.48  --bmc1_pre_inst_reach_state             false
% 7.61/1.48  --bmc1_out_unsat_core                   false
% 7.61/1.48  --bmc1_aig_witness_out                  false
% 7.61/1.48  --bmc1_verbose                          false
% 7.61/1.48  --bmc1_dump_clauses_tptp                false
% 7.61/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.61/1.48  --bmc1_dump_file                        -
% 7.61/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.61/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.61/1.48  --bmc1_ucm_extend_mode                  1
% 7.61/1.48  --bmc1_ucm_init_mode                    2
% 7.61/1.48  --bmc1_ucm_cone_mode                    none
% 7.61/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.61/1.48  --bmc1_ucm_relax_model                  4
% 7.61/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.61/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.61/1.48  --bmc1_ucm_layered_model                none
% 7.61/1.48  --bmc1_ucm_max_lemma_size               10
% 7.61/1.48  
% 7.61/1.48  ------ AIG Options
% 7.61/1.48  
% 7.61/1.48  --aig_mode                              false
% 7.61/1.48  
% 7.61/1.48  ------ Instantiation Options
% 7.61/1.48  
% 7.61/1.48  --instantiation_flag                    true
% 7.61/1.48  --inst_sos_flag                         false
% 7.61/1.48  --inst_sos_phase                        true
% 7.61/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.61/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.61/1.48  --inst_lit_sel_side                     num_symb
% 7.61/1.48  --inst_solver_per_active                1400
% 7.61/1.48  --inst_solver_calls_frac                1.
% 7.61/1.48  --inst_passive_queue_type               priority_queues
% 7.61/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.61/1.48  --inst_passive_queues_freq              [25;2]
% 7.61/1.48  --inst_dismatching                      true
% 7.61/1.48  --inst_eager_unprocessed_to_passive     true
% 7.61/1.48  --inst_prop_sim_given                   true
% 7.61/1.48  --inst_prop_sim_new                     false
% 7.61/1.48  --inst_subs_new                         false
% 7.61/1.48  --inst_eq_res_simp                      false
% 7.61/1.48  --inst_subs_given                       false
% 7.61/1.48  --inst_orphan_elimination               true
% 7.61/1.48  --inst_learning_loop_flag               true
% 7.61/1.48  --inst_learning_start                   3000
% 7.61/1.48  --inst_learning_factor                  2
% 7.61/1.48  --inst_start_prop_sim_after_learn       3
% 7.61/1.48  --inst_sel_renew                        solver
% 7.61/1.48  --inst_lit_activity_flag                true
% 7.61/1.48  --inst_restr_to_given                   false
% 7.61/1.48  --inst_activity_threshold               500
% 7.61/1.48  --inst_out_proof                        true
% 7.61/1.48  
% 7.61/1.48  ------ Resolution Options
% 7.61/1.48  
% 7.61/1.48  --resolution_flag                       true
% 7.61/1.48  --res_lit_sel                           adaptive
% 7.61/1.48  --res_lit_sel_side                      none
% 7.61/1.48  --res_ordering                          kbo
% 7.61/1.48  --res_to_prop_solver                    active
% 7.61/1.48  --res_prop_simpl_new                    false
% 7.61/1.48  --res_prop_simpl_given                  true
% 7.61/1.48  --res_passive_queue_type                priority_queues
% 7.61/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.61/1.48  --res_passive_queues_freq               [15;5]
% 7.61/1.48  --res_forward_subs                      full
% 7.61/1.48  --res_backward_subs                     full
% 7.61/1.48  --res_forward_subs_resolution           true
% 7.61/1.48  --res_backward_subs_resolution          true
% 7.61/1.48  --res_orphan_elimination                true
% 7.61/1.48  --res_time_limit                        2.
% 7.61/1.48  --res_out_proof                         true
% 7.61/1.48  
% 7.61/1.48  ------ Superposition Options
% 7.61/1.48  
% 7.61/1.48  --superposition_flag                    true
% 7.61/1.48  --sup_passive_queue_type                priority_queues
% 7.61/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.61/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.61/1.48  --demod_completeness_check              fast
% 7.61/1.48  --demod_use_ground                      true
% 7.61/1.48  --sup_to_prop_solver                    passive
% 7.61/1.48  --sup_prop_simpl_new                    true
% 7.61/1.48  --sup_prop_simpl_given                  true
% 7.61/1.48  --sup_fun_splitting                     false
% 7.61/1.48  --sup_smt_interval                      50000
% 7.61/1.48  
% 7.61/1.48  ------ Superposition Simplification Setup
% 7.61/1.48  
% 7.61/1.48  --sup_indices_passive                   []
% 7.61/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.61/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.61/1.48  --sup_full_bw                           [BwDemod]
% 7.61/1.48  --sup_immed_triv                        [TrivRules]
% 7.61/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.61/1.48  --sup_immed_bw_main                     []
% 7.61/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.61/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.61/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.61/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.61/1.48  
% 7.61/1.48  ------ Combination Options
% 7.61/1.48  
% 7.61/1.48  --comb_res_mult                         3
% 7.61/1.48  --comb_sup_mult                         2
% 7.61/1.48  --comb_inst_mult                        10
% 7.61/1.48  
% 7.61/1.48  ------ Debug Options
% 7.61/1.48  
% 7.61/1.48  --dbg_backtrace                         false
% 7.61/1.48  --dbg_dump_prop_clauses                 false
% 7.61/1.48  --dbg_dump_prop_clauses_file            -
% 7.61/1.48  --dbg_out_stat                          false
% 7.61/1.48  ------ Parsing...
% 7.61/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.48  ------ Proving...
% 7.61/1.48  ------ Problem Properties 
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  clauses                                 37
% 7.61/1.48  conjectures                             5
% 7.61/1.48  EPR                                     2
% 7.61/1.48  Horn                                    28
% 7.61/1.48  unary                                   7
% 7.61/1.48  binary                                  12
% 7.61/1.48  lits                                    106
% 7.61/1.48  lits eq                                 34
% 7.61/1.48  fd_pure                                 0
% 7.61/1.48  fd_pseudo                               0
% 7.61/1.48  fd_cond                                 6
% 7.61/1.48  fd_pseudo_cond                          5
% 7.61/1.48  AC symbols                              0
% 7.61/1.48  
% 7.61/1.48  ------ Schedule dynamic 5 is on 
% 7.61/1.48  
% 7.61/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ 
% 7.61/1.48  Current options:
% 7.61/1.48  ------ 
% 7.61/1.48  
% 7.61/1.48  ------ Input Options
% 7.61/1.48  
% 7.61/1.48  --out_options                           all
% 7.61/1.48  --tptp_safe_out                         true
% 7.61/1.48  --problem_path                          ""
% 7.61/1.48  --include_path                          ""
% 7.61/1.48  --clausifier                            res/vclausify_rel
% 7.61/1.48  --clausifier_options                    --mode clausify
% 7.61/1.48  --stdin                                 false
% 7.61/1.48  --stats_out                             all
% 7.61/1.48  
% 7.61/1.48  ------ General Options
% 7.61/1.48  
% 7.61/1.48  --fof                                   false
% 7.61/1.48  --time_out_real                         305.
% 7.61/1.48  --time_out_virtual                      -1.
% 7.61/1.48  --symbol_type_check                     false
% 7.61/1.48  --clausify_out                          false
% 7.61/1.48  --sig_cnt_out                           false
% 7.61/1.48  --trig_cnt_out                          false
% 7.61/1.48  --trig_cnt_out_tolerance                1.
% 7.61/1.48  --trig_cnt_out_sk_spl                   false
% 7.61/1.48  --abstr_cl_out                          false
% 7.61/1.48  
% 7.61/1.48  ------ Global Options
% 7.61/1.48  
% 7.61/1.48  --schedule                              default
% 7.61/1.48  --add_important_lit                     false
% 7.61/1.48  --prop_solver_per_cl                    1000
% 7.61/1.48  --min_unsat_core                        false
% 7.61/1.48  --soft_assumptions                      false
% 7.61/1.48  --soft_lemma_size                       3
% 7.61/1.48  --prop_impl_unit_size                   0
% 7.61/1.48  --prop_impl_unit                        []
% 7.61/1.48  --share_sel_clauses                     true
% 7.61/1.48  --reset_solvers                         false
% 7.61/1.48  --bc_imp_inh                            [conj_cone]
% 7.61/1.48  --conj_cone_tolerance                   3.
% 7.61/1.48  --extra_neg_conj                        none
% 7.61/1.48  --large_theory_mode                     true
% 7.61/1.48  --prolific_symb_bound                   200
% 7.61/1.48  --lt_threshold                          2000
% 7.61/1.48  --clause_weak_htbl                      true
% 7.61/1.48  --gc_record_bc_elim                     false
% 7.61/1.48  
% 7.61/1.48  ------ Preprocessing Options
% 7.61/1.48  
% 7.61/1.48  --preprocessing_flag                    true
% 7.61/1.48  --time_out_prep_mult                    0.1
% 7.61/1.48  --splitting_mode                        input
% 7.61/1.48  --splitting_grd                         true
% 7.61/1.48  --splitting_cvd                         false
% 7.61/1.48  --splitting_cvd_svl                     false
% 7.61/1.48  --splitting_nvd                         32
% 7.61/1.48  --sub_typing                            true
% 7.61/1.48  --prep_gs_sim                           true
% 7.61/1.48  --prep_unflatten                        true
% 7.61/1.48  --prep_res_sim                          true
% 7.61/1.48  --prep_upred                            true
% 7.61/1.48  --prep_sem_filter                       exhaustive
% 7.61/1.48  --prep_sem_filter_out                   false
% 7.61/1.48  --pred_elim                             true
% 7.61/1.48  --res_sim_input                         true
% 7.61/1.48  --eq_ax_congr_red                       true
% 7.61/1.48  --pure_diseq_elim                       true
% 7.61/1.48  --brand_transform                       false
% 7.61/1.48  --non_eq_to_eq                          false
% 7.61/1.48  --prep_def_merge                        true
% 7.61/1.48  --prep_def_merge_prop_impl              false
% 7.61/1.48  --prep_def_merge_mbd                    true
% 7.61/1.48  --prep_def_merge_tr_red                 false
% 7.61/1.48  --prep_def_merge_tr_cl                  false
% 7.61/1.48  --smt_preprocessing                     true
% 7.61/1.48  --smt_ac_axioms                         fast
% 7.61/1.48  --preprocessed_out                      false
% 7.61/1.48  --preprocessed_stats                    false
% 7.61/1.48  
% 7.61/1.48  ------ Abstraction refinement Options
% 7.61/1.48  
% 7.61/1.48  --abstr_ref                             []
% 7.61/1.48  --abstr_ref_prep                        false
% 7.61/1.48  --abstr_ref_until_sat                   false
% 7.61/1.48  --abstr_ref_sig_restrict                funpre
% 7.61/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.61/1.48  --abstr_ref_under                       []
% 7.61/1.48  
% 7.61/1.48  ------ SAT Options
% 7.61/1.48  
% 7.61/1.48  --sat_mode                              false
% 7.61/1.48  --sat_fm_restart_options                ""
% 7.61/1.48  --sat_gr_def                            false
% 7.61/1.48  --sat_epr_types                         true
% 7.61/1.48  --sat_non_cyclic_types                  false
% 7.61/1.48  --sat_finite_models                     false
% 7.61/1.48  --sat_fm_lemmas                         false
% 7.61/1.48  --sat_fm_prep                           false
% 7.61/1.48  --sat_fm_uc_incr                        true
% 7.61/1.48  --sat_out_model                         small
% 7.61/1.48  --sat_out_clauses                       false
% 7.61/1.48  
% 7.61/1.48  ------ QBF Options
% 7.61/1.48  
% 7.61/1.48  --qbf_mode                              false
% 7.61/1.48  --qbf_elim_univ                         false
% 7.61/1.48  --qbf_dom_inst                          none
% 7.61/1.48  --qbf_dom_pre_inst                      false
% 7.61/1.48  --qbf_sk_in                             false
% 7.61/1.48  --qbf_pred_elim                         true
% 7.61/1.48  --qbf_split                             512
% 7.61/1.48  
% 7.61/1.48  ------ BMC1 Options
% 7.61/1.48  
% 7.61/1.48  --bmc1_incremental                      false
% 7.61/1.48  --bmc1_axioms                           reachable_all
% 7.61/1.48  --bmc1_min_bound                        0
% 7.61/1.48  --bmc1_max_bound                        -1
% 7.61/1.48  --bmc1_max_bound_default                -1
% 7.61/1.48  --bmc1_symbol_reachability              true
% 7.61/1.48  --bmc1_property_lemmas                  false
% 7.61/1.48  --bmc1_k_induction                      false
% 7.61/1.48  --bmc1_non_equiv_states                 false
% 7.61/1.48  --bmc1_deadlock                         false
% 7.61/1.48  --bmc1_ucm                              false
% 7.61/1.48  --bmc1_add_unsat_core                   none
% 7.61/1.48  --bmc1_unsat_core_children              false
% 7.61/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.61/1.48  --bmc1_out_stat                         full
% 7.61/1.48  --bmc1_ground_init                      false
% 7.61/1.48  --bmc1_pre_inst_next_state              false
% 7.61/1.48  --bmc1_pre_inst_state                   false
% 7.61/1.48  --bmc1_pre_inst_reach_state             false
% 7.61/1.48  --bmc1_out_unsat_core                   false
% 7.61/1.48  --bmc1_aig_witness_out                  false
% 7.61/1.48  --bmc1_verbose                          false
% 7.61/1.48  --bmc1_dump_clauses_tptp                false
% 7.61/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.61/1.48  --bmc1_dump_file                        -
% 7.61/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.61/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.61/1.48  --bmc1_ucm_extend_mode                  1
% 7.61/1.48  --bmc1_ucm_init_mode                    2
% 7.61/1.48  --bmc1_ucm_cone_mode                    none
% 7.61/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.61/1.48  --bmc1_ucm_relax_model                  4
% 7.61/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.61/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.61/1.48  --bmc1_ucm_layered_model                none
% 7.61/1.48  --bmc1_ucm_max_lemma_size               10
% 7.61/1.48  
% 7.61/1.48  ------ AIG Options
% 7.61/1.48  
% 7.61/1.48  --aig_mode                              false
% 7.61/1.48  
% 7.61/1.48  ------ Instantiation Options
% 7.61/1.48  
% 7.61/1.48  --instantiation_flag                    true
% 7.61/1.48  --inst_sos_flag                         false
% 7.61/1.48  --inst_sos_phase                        true
% 7.61/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.61/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.61/1.48  --inst_lit_sel_side                     none
% 7.61/1.48  --inst_solver_per_active                1400
% 7.61/1.48  --inst_solver_calls_frac                1.
% 7.61/1.48  --inst_passive_queue_type               priority_queues
% 7.61/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.61/1.48  --inst_passive_queues_freq              [25;2]
% 7.61/1.48  --inst_dismatching                      true
% 7.61/1.48  --inst_eager_unprocessed_to_passive     true
% 7.61/1.48  --inst_prop_sim_given                   true
% 7.61/1.48  --inst_prop_sim_new                     false
% 7.61/1.48  --inst_subs_new                         false
% 7.61/1.48  --inst_eq_res_simp                      false
% 7.61/1.48  --inst_subs_given                       false
% 7.61/1.48  --inst_orphan_elimination               true
% 7.61/1.48  --inst_learning_loop_flag               true
% 7.61/1.48  --inst_learning_start                   3000
% 7.61/1.48  --inst_learning_factor                  2
% 7.61/1.48  --inst_start_prop_sim_after_learn       3
% 7.61/1.48  --inst_sel_renew                        solver
% 7.61/1.48  --inst_lit_activity_flag                true
% 7.61/1.48  --inst_restr_to_given                   false
% 7.61/1.48  --inst_activity_threshold               500
% 7.61/1.48  --inst_out_proof                        true
% 7.61/1.48  
% 7.61/1.48  ------ Resolution Options
% 7.61/1.48  
% 7.61/1.48  --resolution_flag                       false
% 7.61/1.48  --res_lit_sel                           adaptive
% 7.61/1.48  --res_lit_sel_side                      none
% 7.61/1.48  --res_ordering                          kbo
% 7.61/1.48  --res_to_prop_solver                    active
% 7.61/1.48  --res_prop_simpl_new                    false
% 7.61/1.48  --res_prop_simpl_given                  true
% 7.61/1.48  --res_passive_queue_type                priority_queues
% 7.61/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.61/1.48  --res_passive_queues_freq               [15;5]
% 7.61/1.48  --res_forward_subs                      full
% 7.61/1.48  --res_backward_subs                     full
% 7.61/1.48  --res_forward_subs_resolution           true
% 7.61/1.48  --res_backward_subs_resolution          true
% 7.61/1.48  --res_orphan_elimination                true
% 7.61/1.48  --res_time_limit                        2.
% 7.61/1.48  --res_out_proof                         true
% 7.61/1.48  
% 7.61/1.48  ------ Superposition Options
% 7.61/1.48  
% 7.61/1.48  --superposition_flag                    true
% 7.61/1.48  --sup_passive_queue_type                priority_queues
% 7.61/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.61/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.61/1.48  --demod_completeness_check              fast
% 7.61/1.48  --demod_use_ground                      true
% 7.61/1.48  --sup_to_prop_solver                    passive
% 7.61/1.48  --sup_prop_simpl_new                    true
% 7.61/1.48  --sup_prop_simpl_given                  true
% 7.61/1.48  --sup_fun_splitting                     false
% 7.61/1.48  --sup_smt_interval                      50000
% 7.61/1.48  
% 7.61/1.48  ------ Superposition Simplification Setup
% 7.61/1.48  
% 7.61/1.48  --sup_indices_passive                   []
% 7.61/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.61/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.61/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.61/1.48  --sup_full_bw                           [BwDemod]
% 7.61/1.48  --sup_immed_triv                        [TrivRules]
% 7.61/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.61/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.61/1.48  --sup_immed_bw_main                     []
% 7.61/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.61/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.61/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.61/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.61/1.48  
% 7.61/1.48  ------ Combination Options
% 7.61/1.48  
% 7.61/1.48  --comb_res_mult                         3
% 7.61/1.48  --comb_sup_mult                         2
% 7.61/1.48  --comb_inst_mult                        10
% 7.61/1.48  
% 7.61/1.48  ------ Debug Options
% 7.61/1.48  
% 7.61/1.48  --dbg_backtrace                         false
% 7.61/1.48  --dbg_dump_prop_clauses                 false
% 7.61/1.48  --dbg_dump_prop_clauses_file            -
% 7.61/1.48  --dbg_out_stat                          false
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  ------ Proving...
% 7.61/1.48  
% 7.61/1.48  
% 7.61/1.48  % SZS status Theorem for theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.48  
% 7.61/1.48  fof(f4,axiom,(
% 7.61/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f12,plain,(
% 7.61/1.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.61/1.48    inference(ennf_transformation,[],[f4])).
% 7.61/1.48  
% 7.61/1.48  fof(f13,plain,(
% 7.61/1.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(flattening,[],[f12])).
% 7.61/1.48  
% 7.61/1.48  fof(f29,plain,(
% 7.61/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(nnf_transformation,[],[f13])).
% 7.61/1.48  
% 7.61/1.48  fof(f30,plain,(
% 7.61/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(flattening,[],[f29])).
% 7.61/1.48  
% 7.61/1.48  fof(f31,plain,(
% 7.61/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(rectify,[],[f30])).
% 7.61/1.48  
% 7.61/1.48  fof(f32,plain,(
% 7.61/1.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1) & r2_hidden(sK7(X0,X1),X0)))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f33,plain,(
% 7.61/1.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1) & r2_hidden(sK7(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).
% 7.61/1.48  
% 7.61/1.48  fof(f55,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK7(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f33])).
% 7.61/1.48  
% 7.61/1.48  fof(f75,plain,(
% 7.61/1.48    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK7(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.61/1.48    inference(equality_resolution,[],[f55])).
% 7.61/1.48  
% 7.61/1.48  fof(f5,conjecture,(
% 7.61/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f6,negated_conjecture,(
% 7.61/1.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 7.61/1.48    inference(negated_conjecture,[],[f5])).
% 7.61/1.48  
% 7.61/1.48  fof(f14,plain,(
% 7.61/1.48    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.61/1.48    inference(ennf_transformation,[],[f6])).
% 7.61/1.48  
% 7.61/1.48  fof(f15,plain,(
% 7.61/1.48    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.61/1.48    inference(flattening,[],[f14])).
% 7.61/1.48  
% 7.61/1.48  fof(f35,plain,(
% 7.61/1.48    ( ! [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK9)) != sK9 & k5_relat_1(X0,sK9) = X0 & k1_relat_1(sK9) = k2_relat_1(X0) & v1_funct_1(sK9) & v1_relat_1(sK9))) )),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f34,plain,(
% 7.61/1.48    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(sK8,X1) = sK8 & k1_relat_1(X1) = k2_relat_1(sK8) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK8) & v1_relat_1(sK8))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f36,plain,(
% 7.61/1.48    (k6_relat_1(k1_relat_1(sK9)) != sK9 & k5_relat_1(sK8,sK9) = sK8 & k1_relat_1(sK9) = k2_relat_1(sK8) & v1_funct_1(sK9) & v1_relat_1(sK9)) & v1_funct_1(sK8) & v1_relat_1(sK8)),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f15,f35,f34])).
% 7.61/1.48  
% 7.61/1.48  fof(f60,plain,(
% 7.61/1.48    v1_funct_1(sK9)),
% 7.61/1.48    inference(cnf_transformation,[],[f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f59,plain,(
% 7.61/1.48    v1_relat_1(sK9)),
% 7.61/1.48    inference(cnf_transformation,[],[f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f63,plain,(
% 7.61/1.48    k6_relat_1(k1_relat_1(sK9)) != sK9),
% 7.61/1.48    inference(cnf_transformation,[],[f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f3,axiom,(
% 7.61/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f10,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.61/1.48    inference(ennf_transformation,[],[f3])).
% 7.61/1.48  
% 7.61/1.48  fof(f11,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(flattening,[],[f10])).
% 7.61/1.48  
% 7.61/1.48  fof(f23,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(nnf_transformation,[],[f11])).
% 7.61/1.48  
% 7.61/1.48  fof(f24,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(rectify,[],[f23])).
% 7.61/1.48  
% 7.61/1.48  fof(f27,plain,(
% 7.61/1.48    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f26,plain,(
% 7.61/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) = X2 & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))) )),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f25,plain,(
% 7.61/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f28,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).
% 7.61/1.48  
% 7.61/1.48  fof(f48,plain,(
% 7.61/1.48    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f28])).
% 7.61/1.48  
% 7.61/1.48  fof(f72,plain,(
% 7.61/1.48    ( ! [X0,X5] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(equality_resolution,[],[f48])).
% 7.61/1.48  
% 7.61/1.48  fof(f58,plain,(
% 7.61/1.48    v1_funct_1(sK8)),
% 7.61/1.48    inference(cnf_transformation,[],[f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f57,plain,(
% 7.61/1.48    v1_relat_1(sK8)),
% 7.61/1.48    inference(cnf_transformation,[],[f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f61,plain,(
% 7.61/1.48    k1_relat_1(sK9) = k2_relat_1(sK8)),
% 7.61/1.48    inference(cnf_transformation,[],[f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f2,axiom,(
% 7.61/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f8,plain,(
% 7.61/1.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.61/1.48    inference(ennf_transformation,[],[f2])).
% 7.61/1.48  
% 7.61/1.48  fof(f9,plain,(
% 7.61/1.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(flattening,[],[f8])).
% 7.61/1.48  
% 7.61/1.48  fof(f22,plain,(
% 7.61/1.48    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(nnf_transformation,[],[f9])).
% 7.61/1.48  
% 7.61/1.48  fof(f43,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f22])).
% 7.61/1.48  
% 7.61/1.48  fof(f69,plain,(
% 7.61/1.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(equality_resolution,[],[f43])).
% 7.61/1.48  
% 7.61/1.48  fof(f47,plain,(
% 7.61/1.48    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f28])).
% 7.61/1.48  
% 7.61/1.48  fof(f73,plain,(
% 7.61/1.48    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(equality_resolution,[],[f47])).
% 7.61/1.48  
% 7.61/1.48  fof(f62,plain,(
% 7.61/1.48    k5_relat_1(sK8,sK9) = sK8),
% 7.61/1.48    inference(cnf_transformation,[],[f36])).
% 7.61/1.48  
% 7.61/1.48  fof(f1,axiom,(
% 7.61/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 7.61/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.61/1.48  
% 7.61/1.48  fof(f7,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(ennf_transformation,[],[f1])).
% 7.61/1.48  
% 7.61/1.48  fof(f16,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(nnf_transformation,[],[f7])).
% 7.61/1.48  
% 7.61/1.48  fof(f17,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(rectify,[],[f16])).
% 7.61/1.48  
% 7.61/1.48  fof(f20,plain,(
% 7.61/1.48    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f19,plain,(
% 7.61/1.48    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f18,plain,(
% 7.61/1.48    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 7.61/1.48    introduced(choice_axiom,[])).
% 7.61/1.48  
% 7.61/1.48  fof(f21,plain,(
% 7.61/1.48    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.61/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f20,f19,f18])).
% 7.61/1.48  
% 7.61/1.48  fof(f39,plain,(
% 7.61/1.48    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f21])).
% 7.61/1.48  
% 7.61/1.48  fof(f64,plain,(
% 7.61/1.48    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(equality_resolution,[],[f39])).
% 7.61/1.48  
% 7.61/1.48  fof(f44,plain,(
% 7.61/1.48    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f22])).
% 7.61/1.48  
% 7.61/1.48  fof(f56,plain,(
% 7.61/1.48    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK7(X0,X1)) != sK7(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.61/1.48    inference(cnf_transformation,[],[f33])).
% 7.61/1.48  
% 7.61/1.48  fof(f74,plain,(
% 7.61/1.48    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK7(k1_relat_1(X1),X1)) != sK7(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.61/1.48    inference(equality_resolution,[],[f56])).
% 7.61/1.48  
% 7.61/1.48  cnf(c_17,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0))
% 7.61/1.48      | ~ v1_funct_1(X0)
% 7.61/1.48      | ~ v1_relat_1(X0)
% 7.61/1.48      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 7.61/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_23,negated_conjecture,
% 7.61/1.48      ( v1_funct_1(sK9) ),
% 7.61/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_266,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0))
% 7.61/1.48      | ~ v1_relat_1(X0)
% 7.61/1.48      | k6_relat_1(k1_relat_1(X0)) = X0
% 7.61/1.48      | sK9 != X0 ),
% 7.61/1.48      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_267,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
% 7.61/1.48      | ~ v1_relat_1(sK9)
% 7.61/1.48      | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
% 7.61/1.48      inference(unflattening,[status(thm)],[c_266]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_24,negated_conjecture,
% 7.61/1.48      ( v1_relat_1(sK9) ),
% 7.61/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_20,negated_conjecture,
% 7.61/1.48      ( k6_relat_1(k1_relat_1(sK9)) != sK9 ),
% 7.61/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_38,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
% 7.61/1.48      | ~ v1_funct_1(sK9)
% 7.61/1.48      | ~ v1_relat_1(sK9)
% 7.61/1.48      | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_269,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) ),
% 7.61/1.48      inference(global_propositional_subsumption,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_267,c_24,c_23,c_20,c_38]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1364,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) = iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_14,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.61/1.48      | ~ v1_funct_1(X1)
% 7.61/1.48      | ~ v1_relat_1(X1)
% 7.61/1.48      | k1_funct_1(X1,sK6(X1,X0)) = X0 ),
% 7.61/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_25,negated_conjecture,
% 7.61/1.48      ( v1_funct_1(sK8) ),
% 7.61/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_547,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.61/1.48      | ~ v1_relat_1(X1)
% 7.61/1.48      | k1_funct_1(X1,sK6(X1,X0)) = X0
% 7.61/1.48      | sK8 != X1 ),
% 7.61/1.48      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_548,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_relat_1(sK8))
% 7.61/1.48      | ~ v1_relat_1(sK8)
% 7.61/1.48      | k1_funct_1(sK8,sK6(sK8,X0)) = X0 ),
% 7.61/1.48      inference(unflattening,[status(thm)],[c_547]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_26,negated_conjecture,
% 7.61/1.48      ( v1_relat_1(sK8) ),
% 7.61/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_552,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_relat_1(sK8))
% 7.61/1.48      | k1_funct_1(sK8,sK6(sK8,X0)) = X0 ),
% 7.61/1.48      inference(global_propositional_subsumption,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_548,c_26]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1350,plain,
% 7.61/1.48      ( k1_funct_1(sK8,sK6(sK8,X0)) = X0
% 7.61/1.48      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_22,negated_conjecture,
% 7.61/1.48      ( k1_relat_1(sK9) = k2_relat_1(sK8) ),
% 7.61/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1395,plain,
% 7.61/1.48      ( k1_funct_1(sK8,sK6(sK8,X0)) = X0
% 7.61/1.48      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_1350,c_22]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1957,plain,
% 7.61/1.48      ( k1_funct_1(sK8,sK6(sK8,sK7(k1_relat_1(sK9),sK9))) = sK7(k1_relat_1(sK9),sK9) ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_1364,c_1395]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_9,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.61/1.48      | ~ v1_funct_1(X1)
% 7.61/1.48      | ~ v1_relat_1(X1) ),
% 7.61/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_607,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.61/1.48      | ~ v1_relat_1(X1)
% 7.61/1.48      | sK8 != X1 ),
% 7.61/1.48      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_608,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 7.61/1.48      | ~ v1_relat_1(sK8) ),
% 7.61/1.48      inference(unflattening,[status(thm)],[c_607]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_612,plain,
% 7.61/1.48      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 7.61/1.48      | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
% 7.61/1.48      inference(global_propositional_subsumption,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_608,c_26]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_613,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
% 7.61/1.48      inference(renaming,[status(thm)],[c_612]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1347,plain,
% 7.61/1.48      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2306,plain,
% 7.61/1.48      ( r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),sK7(k1_relat_1(sK9),sK9)),sK8) = iProver_top ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_1957,c_1347]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_29,plain,
% 7.61/1.48      ( v1_relat_1(sK9) = iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_30,plain,
% 7.61/1.48      ( v1_funct_1(sK9) = iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_37,plain,
% 7.61/1.48      ( k6_relat_1(k1_relat_1(X0)) = X0
% 7.61/1.48      | r2_hidden(sK7(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
% 7.61/1.48      | v1_funct_1(X0) != iProver_top
% 7.61/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_39,plain,
% 7.61/1.48      ( k6_relat_1(k1_relat_1(sK9)) = sK9
% 7.61/1.48      | r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) = iProver_top
% 7.61/1.48      | v1_funct_1(sK9) != iProver_top
% 7.61/1.48      | v1_relat_1(sK9) != iProver_top ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_37]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_817,plain,( X0 = X0 ),theory(equality) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1904,plain,
% 7.61/1.48      ( k2_relat_1(sK8) = k2_relat_1(sK8) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_817]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2312,plain,
% 7.61/1.48      ( sK7(k1_relat_1(sK9),sK9) = sK7(k1_relat_1(sK9),sK9) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_817]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_818,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1822,plain,
% 7.61/1.48      ( X0 != X1 | X0 = k1_relat_1(sK9) | k1_relat_1(sK9) != X1 ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_818]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2330,plain,
% 7.61/1.48      ( X0 != k2_relat_1(sK8)
% 7.61/1.48      | X0 = k1_relat_1(sK9)
% 7.61/1.48      | k1_relat_1(sK9) != k2_relat_1(sK8) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_1822]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2519,plain,
% 7.61/1.48      ( k2_relat_1(sK8) != k2_relat_1(sK8)
% 7.61/1.48      | k2_relat_1(sK8) = k1_relat_1(sK9)
% 7.61/1.48      | k1_relat_1(sK9) != k2_relat_1(sK8) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_2330]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_821,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.61/1.48      theory(equality) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1722,plain,
% 7.61/1.48      ( r2_hidden(X0,X1)
% 7.61/1.48      | ~ r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
% 7.61/1.48      | X0 != sK7(k1_relat_1(sK9),sK9)
% 7.61/1.48      | X1 != k1_relat_1(sK9) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_821]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1839,plain,
% 7.61/1.48      ( r2_hidden(X0,k2_relat_1(sK8))
% 7.61/1.48      | ~ r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
% 7.61/1.48      | X0 != sK7(k1_relat_1(sK9),sK9)
% 7.61/1.48      | k2_relat_1(sK8) != k1_relat_1(sK9) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_1722]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4626,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k2_relat_1(sK8))
% 7.61/1.48      | ~ r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9))
% 7.61/1.48      | sK7(k1_relat_1(sK9),sK9) != sK7(k1_relat_1(sK9),sK9)
% 7.61/1.48      | k2_relat_1(sK8) != k1_relat_1(sK9) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_1839]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_4639,plain,
% 7.61/1.48      ( sK7(k1_relat_1(sK9),sK9) != sK7(k1_relat_1(sK9),sK9)
% 7.61/1.48      | k2_relat_1(sK8) != k1_relat_1(sK9)
% 7.61/1.48      | r2_hidden(sK7(k1_relat_1(sK9),sK9),k2_relat_1(sK8)) = iProver_top
% 7.61/1.48      | r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) != iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_4626]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_15,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.61/1.48      | r2_hidden(sK6(X1,X0),k1_relat_1(X1))
% 7.61/1.48      | ~ v1_funct_1(X1)
% 7.61/1.48      | ~ v1_relat_1(X1) ),
% 7.61/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_529,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.61/1.48      | r2_hidden(sK6(X1,X0),k1_relat_1(X1))
% 7.61/1.48      | ~ v1_relat_1(X1)
% 7.61/1.48      | sK8 != X1 ),
% 7.61/1.48      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_530,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_relat_1(sK8))
% 7.61/1.48      | r2_hidden(sK6(sK8,X0),k1_relat_1(sK8))
% 7.61/1.48      | ~ v1_relat_1(sK8) ),
% 7.61/1.48      inference(unflattening,[status(thm)],[c_529]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_534,plain,
% 7.61/1.48      ( r2_hidden(sK6(sK8,X0),k1_relat_1(sK8))
% 7.61/1.48      | ~ r2_hidden(X0,k2_relat_1(sK8)) ),
% 7.61/1.48      inference(global_propositional_subsumption,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_530,c_26]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_535,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k2_relat_1(sK8))
% 7.61/1.48      | r2_hidden(sK6(sK8,X0),k1_relat_1(sK8)) ),
% 7.61/1.48      inference(renaming,[status(thm)],[c_534]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_7305,plain,
% 7.61/1.48      ( ~ r2_hidden(sK7(k1_relat_1(sK9),sK9),k2_relat_1(sK8))
% 7.61/1.48      | r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) ),
% 7.61/1.48      inference(instantiation,[status(thm)],[c_535]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_7306,plain,
% 7.61/1.48      ( r2_hidden(sK7(k1_relat_1(sK9),sK9),k2_relat_1(sK8)) != iProver_top
% 7.61/1.48      | r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) = iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_7305]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_17055,plain,
% 7.61/1.48      ( r2_hidden(k4_tarski(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),sK7(k1_relat_1(sK9),sK9)),sK8) = iProver_top ),
% 7.61/1.48      inference(global_propositional_subsumption,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_2306,c_29,c_30,c_22,c_20,c_39,c_1904,c_2312,c_2519,
% 7.61/1.48                 c_4639,c_7306]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_21,negated_conjecture,
% 7.61/1.48      ( k5_relat_1(sK8,sK9) = sK8 ),
% 7.61/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_472,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.61/1.48      | ~ v1_relat_1(X1)
% 7.61/1.48      | sK9 != X1 ),
% 7.61/1.48      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_473,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
% 7.61/1.48      | ~ v1_relat_1(sK9) ),
% 7.61/1.48      inference(unflattening,[status(thm)],[c_472]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_477,plain,
% 7.61/1.48      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
% 7.61/1.48      | ~ r2_hidden(X0,k1_relat_1(sK9)) ),
% 7.61/1.48      inference(global_propositional_subsumption,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_473,c_24]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_478,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) ),
% 7.61/1.48      inference(renaming,[status(thm)],[c_477]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1354,plain,
% 7.61/1.48      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_3,plain,
% 7.61/1.48      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.61/1.48      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 7.61/1.48      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 7.61/1.48      | ~ v1_relat_1(X2)
% 7.61/1.48      | ~ v1_relat_1(X4)
% 7.61/1.48      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 7.61/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_1369,plain,
% 7.61/1.48      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
% 7.61/1.48      | v1_relat_1(X2) != iProver_top
% 7.61/1.48      | v1_relat_1(X4) != iProver_top
% 7.61/1.48      | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_2617,plain,
% 7.61/1.48      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
% 7.61/1.48      | v1_relat_1(X2) != iProver_top
% 7.61/1.48      | v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top
% 7.61/1.48      | v1_relat_1(sK9) != iProver_top ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_1354,c_1369]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_22633,plain,
% 7.61/1.48      ( v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top
% 7.61/1.48      | v1_relat_1(X2) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 7.61/1.48      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 7.61/1.48      inference(global_propositional_subsumption,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_2617,c_29]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_22634,plain,
% 7.61/1.48      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),k5_relat_1(X2,sK9)) = iProver_top
% 7.61/1.48      | v1_relat_1(X2) != iProver_top
% 7.61/1.48      | v1_relat_1(k5_relat_1(X2,sK9)) != iProver_top ),
% 7.61/1.48      inference(renaming,[status(thm)],[c_22633]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_22645,plain,
% 7.61/1.48      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
% 7.61/1.48      | v1_relat_1(k5_relat_1(sK8,sK9)) != iProver_top
% 7.61/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.61/1.48      inference(superposition,[status(thm)],[c_21,c_22634]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_22694,plain,
% 7.61/1.48      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
% 7.61/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.61/1.48      inference(light_normalisation,[status(thm)],[c_22645,c_21]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_27,plain,
% 7.61/1.48      ( v1_relat_1(sK8) = iProver_top ),
% 7.61/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_22763,plain,
% 7.61/1.48      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
% 7.61/1.48      | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top ),
% 7.61/1.48      inference(global_propositional_subsumption,
% 7.61/1.48                [status(thm)],
% 7.61/1.48                [c_22694,c_27]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_22764,plain,
% 7.61/1.48      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,X0),sK8) != iProver_top
% 7.61/1.48      | r2_hidden(k4_tarski(X1,k1_funct_1(sK9,X0)),sK8) = iProver_top ),
% 7.61/1.48      inference(renaming,[status(thm)],[c_22763]) ).
% 7.61/1.48  
% 7.61/1.48  cnf(c_8,plain,
% 7.61/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.61/1.48      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.61/1.48      | ~ v1_funct_1(X1)
% 7.61/1.48      | ~ v1_relat_1(X1)
% 7.61/1.48      | k1_funct_1(X1,X0) = X2 ),
% 7.61/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_625,plain,
% 7.61/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.61/1.49      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.61/1.49      | ~ v1_relat_1(X1)
% 7.61/1.49      | k1_funct_1(X1,X0) = X2
% 7.61/1.49      | sK8 != X1 ),
% 7.61/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_626,plain,
% 7.61/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 7.61/1.49      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 7.61/1.49      | ~ v1_relat_1(sK8)
% 7.61/1.49      | k1_funct_1(sK8,X0) = X1 ),
% 7.61/1.49      inference(unflattening,[status(thm)],[c_625]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_630,plain,
% 7.61/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 7.61/1.49      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 7.61/1.49      | k1_funct_1(sK8,X0) = X1 ),
% 7.61/1.49      inference(global_propositional_subsumption,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_626,c_26]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_631,plain,
% 7.61/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 7.61/1.49      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 7.61/1.49      | k1_funct_1(sK8,X0) = X1 ),
% 7.61/1.49      inference(renaming,[status(thm)],[c_630]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_1346,plain,
% 7.61/1.49      ( k1_funct_1(sK8,X0) = X1
% 7.61/1.49      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 7.61/1.49      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 7.61/1.49      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_22776,plain,
% 7.61/1.49      ( k1_funct_1(sK8,X0) = k1_funct_1(sK9,X1)
% 7.61/1.49      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 7.61/1.49      | r2_hidden(X1,k1_relat_1(sK9)) != iProver_top
% 7.61/1.49      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_22764,c_1346]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_23091,plain,
% 7.61/1.49      ( k1_funct_1(sK8,sK6(sK8,sK7(k1_relat_1(sK9),sK9))) = k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9))
% 7.61/1.49      | r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) != iProver_top
% 7.61/1.49      | r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) != iProver_top ),
% 7.61/1.49      inference(superposition,[status(thm)],[c_17055,c_22776]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_23106,plain,
% 7.61/1.49      ( k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) = sK7(k1_relat_1(sK9),sK9)
% 7.61/1.49      | r2_hidden(sK7(k1_relat_1(sK9),sK9),k1_relat_1(sK9)) != iProver_top
% 7.61/1.49      | r2_hidden(sK6(sK8,sK7(k1_relat_1(sK9),sK9)),k1_relat_1(sK8)) != iProver_top ),
% 7.61/1.49      inference(light_normalisation,[status(thm)],[c_23091,c_1957]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_16,plain,
% 7.61/1.49      ( ~ v1_funct_1(X0)
% 7.61/1.49      | ~ v1_relat_1(X0)
% 7.61/1.49      | k1_funct_1(X0,sK7(k1_relat_1(X0),X0)) != sK7(k1_relat_1(X0),X0)
% 7.61/1.49      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 7.61/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(c_41,plain,
% 7.61/1.49      ( ~ v1_funct_1(sK9)
% 7.61/1.49      | ~ v1_relat_1(sK9)
% 7.61/1.49      | k1_funct_1(sK9,sK7(k1_relat_1(sK9),sK9)) != sK7(k1_relat_1(sK9),sK9)
% 7.61/1.49      | k6_relat_1(k1_relat_1(sK9)) = sK9 ),
% 7.61/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.61/1.49  
% 7.61/1.49  cnf(contradiction,plain,
% 7.61/1.49      ( $false ),
% 7.61/1.49      inference(minisat,
% 7.61/1.49                [status(thm)],
% 7.61/1.49                [c_23106,c_7306,c_4639,c_2519,c_2312,c_1904,c_41,c_39,
% 7.61/1.49                 c_20,c_22,c_30,c_23,c_29,c_24]) ).
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  ------                               Statistics
% 7.61/1.49  
% 7.61/1.49  ------ General
% 7.61/1.49  
% 7.61/1.49  abstr_ref_over_cycles:                  0
% 7.61/1.49  abstr_ref_under_cycles:                 0
% 7.61/1.49  gc_basic_clause_elim:                   0
% 7.61/1.49  forced_gc_time:                         0
% 7.61/1.49  parsing_time:                           0.009
% 7.61/1.49  unif_index_cands_time:                  0.
% 7.61/1.49  unif_index_add_time:                    0.
% 7.61/1.49  orderings_time:                         0.
% 7.61/1.49  out_proof_time:                         0.01
% 7.61/1.49  total_time:                             0.984
% 7.61/1.49  num_of_symbols:                         51
% 7.61/1.49  num_of_terms:                           16571
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing
% 7.61/1.49  
% 7.61/1.49  num_of_splits:                          0
% 7.61/1.49  num_of_split_atoms:                     0
% 7.61/1.49  num_of_reused_defs:                     0
% 7.61/1.49  num_eq_ax_congr_red:                    36
% 7.61/1.49  num_of_sem_filtered_clauses:            1
% 7.61/1.49  num_of_subtypes:                        0
% 7.61/1.49  monotx_restored_types:                  0
% 7.61/1.49  sat_num_of_epr_types:                   0
% 7.61/1.49  sat_num_of_non_cyclic_types:            0
% 7.61/1.49  sat_guarded_non_collapsed_types:        0
% 7.61/1.49  num_pure_diseq_elim:                    0
% 7.61/1.49  simp_replaced_by:                       0
% 7.61/1.49  res_preprocessed:                       129
% 7.61/1.49  prep_upred:                             0
% 7.61/1.49  prep_unflattend:                        22
% 7.61/1.49  smt_new_axioms:                         0
% 7.61/1.49  pred_elim_cands:                        3
% 7.61/1.49  pred_elim:                              1
% 7.61/1.49  pred_elim_cl:                           -11
% 7.61/1.49  pred_elim_cycles:                       2
% 7.61/1.49  merged_defs:                            0
% 7.61/1.49  merged_defs_ncl:                        0
% 7.61/1.49  bin_hyper_res:                          0
% 7.61/1.49  prep_cycles:                            3
% 7.61/1.49  pred_elim_time:                         0.009
% 7.61/1.49  splitting_time:                         0.
% 7.61/1.49  sem_filter_time:                        0.
% 7.61/1.49  monotx_time:                            0.
% 7.61/1.49  subtype_inf_time:                       0.
% 7.61/1.49  
% 7.61/1.49  ------ Problem properties
% 7.61/1.49  
% 7.61/1.49  clauses:                                37
% 7.61/1.49  conjectures:                            5
% 7.61/1.49  epr:                                    2
% 7.61/1.49  horn:                                   28
% 7.61/1.49  ground:                                 9
% 7.61/1.49  unary:                                  7
% 7.61/1.49  binary:                                 12
% 7.61/1.49  lits:                                   106
% 7.61/1.49  lits_eq:                                34
% 7.61/1.49  fd_pure:                                0
% 7.61/1.49  fd_pseudo:                              0
% 7.61/1.49  fd_cond:                                6
% 7.61/1.49  fd_pseudo_cond:                         5
% 7.61/1.49  ac_symbols:                             0
% 7.61/1.49  
% 7.61/1.49  ------ Propositional Solver
% 7.61/1.49  
% 7.61/1.49  prop_solver_calls:                      24
% 7.61/1.49  prop_fast_solver_calls:                 1301
% 7.61/1.49  smt_solver_calls:                       0
% 7.61/1.49  smt_fast_solver_calls:                  0
% 7.61/1.49  prop_num_of_clauses:                    6574
% 7.61/1.49  prop_preprocess_simplified:             7686
% 7.61/1.49  prop_fo_subsumed:                       30
% 7.61/1.49  prop_solver_time:                       0.
% 7.61/1.49  smt_solver_time:                        0.
% 7.61/1.49  smt_fast_solver_time:                   0.
% 7.61/1.49  prop_fast_solver_time:                  0.
% 7.61/1.49  prop_unsat_core_time:                   0.
% 7.61/1.49  
% 7.61/1.49  ------ QBF
% 7.61/1.49  
% 7.61/1.49  qbf_q_res:                              0
% 7.61/1.49  qbf_num_tautologies:                    0
% 7.61/1.49  qbf_prep_cycles:                        0
% 7.61/1.49  
% 7.61/1.49  ------ BMC1
% 7.61/1.49  
% 7.61/1.49  bmc1_current_bound:                     -1
% 7.61/1.49  bmc1_last_solved_bound:                 -1
% 7.61/1.49  bmc1_unsat_core_size:                   -1
% 7.61/1.49  bmc1_unsat_core_parents_size:           -1
% 7.61/1.49  bmc1_merge_next_fun:                    0
% 7.61/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.61/1.49  
% 7.61/1.49  ------ Instantiation
% 7.61/1.49  
% 7.61/1.49  inst_num_of_clauses:                    1053
% 7.61/1.49  inst_num_in_passive:                    297
% 7.61/1.49  inst_num_in_active:                     593
% 7.61/1.49  inst_num_in_unprocessed:                164
% 7.61/1.49  inst_num_of_loops:                      710
% 7.61/1.49  inst_num_of_learning_restarts:          0
% 7.61/1.49  inst_num_moves_active_passive:          113
% 7.61/1.49  inst_lit_activity:                      0
% 7.61/1.49  inst_lit_activity_moves:                0
% 7.61/1.49  inst_num_tautologies:                   0
% 7.61/1.49  inst_num_prop_implied:                  0
% 7.61/1.49  inst_num_existing_simplified:           0
% 7.61/1.49  inst_num_eq_res_simplified:             0
% 7.61/1.49  inst_num_child_elim:                    0
% 7.61/1.49  inst_num_of_dismatching_blockings:      407
% 7.61/1.49  inst_num_of_non_proper_insts:           1184
% 7.61/1.49  inst_num_of_duplicates:                 0
% 7.61/1.49  inst_inst_num_from_inst_to_res:         0
% 7.61/1.49  inst_dismatching_checking_time:         0.
% 7.61/1.49  
% 7.61/1.49  ------ Resolution
% 7.61/1.49  
% 7.61/1.49  res_num_of_clauses:                     0
% 7.61/1.49  res_num_in_passive:                     0
% 7.61/1.49  res_num_in_active:                      0
% 7.61/1.49  res_num_of_loops:                       132
% 7.61/1.49  res_forward_subset_subsumed:            156
% 7.61/1.49  res_backward_subset_subsumed:           2
% 7.61/1.49  res_forward_subsumed:                   0
% 7.61/1.49  res_backward_subsumed:                  0
% 7.61/1.49  res_forward_subsumption_resolution:     0
% 7.61/1.49  res_backward_subsumption_resolution:    0
% 7.61/1.49  res_clause_to_clause_subsumption:       5415
% 7.61/1.49  res_orphan_elimination:                 0
% 7.61/1.49  res_tautology_del:                      194
% 7.61/1.49  res_num_eq_res_simplified:              0
% 7.61/1.49  res_num_sel_changes:                    0
% 7.61/1.49  res_moves_from_active_to_pass:          0
% 7.61/1.49  
% 7.61/1.49  ------ Superposition
% 7.61/1.49  
% 7.61/1.49  sup_time_total:                         0.
% 7.61/1.49  sup_time_generating:                    0.
% 7.61/1.49  sup_time_sim_full:                      0.
% 7.61/1.49  sup_time_sim_immed:                     0.
% 7.61/1.49  
% 7.61/1.49  sup_num_of_clauses:                     1544
% 7.61/1.49  sup_num_in_active:                      142
% 7.61/1.49  sup_num_in_passive:                     1402
% 7.61/1.49  sup_num_of_loops:                       141
% 7.61/1.49  sup_fw_superposition:                   1300
% 7.61/1.49  sup_bw_superposition:                   522
% 7.61/1.49  sup_immediate_simplified:               41
% 7.61/1.49  sup_given_eliminated:                   0
% 7.61/1.49  comparisons_done:                       0
% 7.61/1.49  comparisons_avoided:                    88
% 7.61/1.49  
% 7.61/1.49  ------ Simplifications
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  sim_fw_subset_subsumed:                 4
% 7.61/1.49  sim_bw_subset_subsumed:                 0
% 7.61/1.49  sim_fw_subsumed:                        3
% 7.61/1.49  sim_bw_subsumed:                        0
% 7.61/1.49  sim_fw_subsumption_res:                 0
% 7.61/1.49  sim_bw_subsumption_res:                 0
% 7.61/1.49  sim_tautology_del:                      1
% 7.61/1.49  sim_eq_tautology_del:                   265
% 7.61/1.49  sim_eq_res_simp:                        0
% 7.61/1.49  sim_fw_demodulated:                     3
% 7.61/1.49  sim_bw_demodulated:                     0
% 7.61/1.49  sim_light_normalised:                   37
% 7.61/1.49  sim_joinable_taut:                      0
% 7.61/1.49  sim_joinable_simp:                      0
% 7.61/1.49  sim_ac_normalised:                      0
% 7.61/1.49  sim_smt_subsumption:                    0
% 7.61/1.49  
%------------------------------------------------------------------------------

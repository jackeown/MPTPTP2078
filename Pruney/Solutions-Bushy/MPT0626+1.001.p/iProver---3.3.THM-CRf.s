%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0626+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:45 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 902 expanded)
%              Number of clauses        :   82 ( 235 expanded)
%              Number of leaves         :   15 ( 223 expanded)
%              Depth                    :   26
%              Number of atoms          :  584 (6152 expanded)
%              Number of equality atoms :  192 ( 692 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ( ~ r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(X1))
          | ~ r2_hidden(X0,k1_relat_1(sK9))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK9,X1))) )
        & ( ( r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(X1))
            & r2_hidden(X0,k1_relat_1(sK9)) )
          | r2_hidden(X0,k1_relat_1(k5_relat_1(sK9,X1))) )
        & v1_funct_1(sK9)
        & v1_relat_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2))
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,sK7),k1_relat_1(sK8))
            | ~ r2_hidden(sK7,k1_relat_1(X2))
            | ~ r2_hidden(sK7,k1_relat_1(k5_relat_1(X2,sK8))) )
          & ( ( r2_hidden(k1_funct_1(X2,sK7),k1_relat_1(sK8))
              & r2_hidden(sK7,k1_relat_1(X2)) )
            | r2_hidden(sK7,k1_relat_1(k5_relat_1(X2,sK8))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8))
      | ~ r2_hidden(sK7,k1_relat_1(sK9))
      | ~ r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) )
    & ( ( r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8))
        & r2_hidden(sK7,k1_relat_1(sK9)) )
      | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) )
    & v1_funct_1(sK9)
    & v1_relat_1(sK9)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f30,f29])).

fof(f52,plain,
    ( r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8))
    | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(flattening,[],[f7])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f50,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f22,f25,f24,f23])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19,f18,f17])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f51,plain,
    ( r2_hidden(sK7,k1_relat_1(sK9))
    | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f40,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f53,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8))
    | ~ r2_hidden(sK7,k1_relat_1(sK9))
    | ~ r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8))
    | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_748,plain,
    ( r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_242,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_243,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
    | ~ v1_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_247,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9)
    | ~ r2_hidden(X0,k1_relat_1(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_19])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_744,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK9,X0)),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_278,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_283,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_21])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_742,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_753,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top
    | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_750,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_855,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_753,c_750])).

cnf(c_5892,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK8,X0)),k5_relat_1(X2,sK8)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_742,c_855])).

cnf(c_22,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7188,plain,
    ( v1_relat_1(X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK8,X0)),k5_relat_1(X2,sK8)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5892,c_22])).

cnf(c_7189,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK8,X0)),k5_relat_1(X2,sK8)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7188])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_758,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7202,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK8))) = iProver_top
    | r2_hidden(X2,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7189,c_758])).

cnf(c_16048,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_7202])).

cnf(c_24,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17946,plain,
    ( r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16048,c_24])).

cnf(c_17947,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17946])).

cnf(c_17955,plain,
    ( r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top
    | r2_hidden(sK7,k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_17947])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8)))
    | r2_hidden(sK7,k1_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_747,plain,
    ( r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top
    | r2_hidden(sK7,k1_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_757,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_751,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_834,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_751,c_750])).

cnf(c_2894,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k5_relat_1(X1,X3)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_758])).

cnf(c_9445,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_757,c_2894])).

cnf(c_9637,plain,
    ( r2_hidden(sK7,k1_relat_1(sK9)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_747,c_9445])).

cnf(c_18024,plain,
    ( r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17955,c_22,c_24,c_9637])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_136,plain,
    ( ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_6])).

cnf(c_137,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_314,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK9 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_137])).

cnf(c_315,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
    | ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_319,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK9)
    | k1_funct_1(sK9,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_19])).

cnf(c_740,plain,
    ( k1_funct_1(sK9,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_2898,plain,
    ( sK6(sK9,X0,X1,X2) = k1_funct_1(sK9,X1)
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK9,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_740])).

cnf(c_3327,plain,
    ( v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK9,X0)) != iProver_top
    | sK6(sK9,X0,X1,X2) = k1_funct_1(sK9,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2898,c_24])).

cnf(c_3328,plain,
    ( sK6(sK9,X0,X1,X2) = k1_funct_1(sK9,X1)
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK9,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3327])).

cnf(c_3335,plain,
    ( sK6(sK9,X0,X1,sK2(k5_relat_1(sK9,X0),X1)) = k1_funct_1(sK9,X1)
    | r2_hidden(X1,k1_relat_1(k5_relat_1(sK9,X0))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_757,c_3328])).

cnf(c_18031,plain,
    ( sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) = k1_funct_1(sK9,sK7)
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_18024,c_3335])).

cnf(c_1187,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k5_relat_1(X0,sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1188,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_1190,plain,
    ( v1_relat_1(k5_relat_1(sK9,sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1188])).

cnf(c_1051,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | r2_hidden(k4_tarski(X0,sK2(k5_relat_1(X1,X2),X0)),k5_relat_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1333,plain,
    ( r2_hidden(k4_tarski(sK7,sK2(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8))
    | ~ r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_1334,plain,
    ( r2_hidden(k4_tarski(sK7,sK2(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8)) = iProver_top
    | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_1384,plain,
    ( r2_hidden(k4_tarski(sK7,sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7))),sK9)
    | ~ r2_hidden(k4_tarski(sK7,sK2(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8))
    | ~ v1_relat_1(k5_relat_1(sK9,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1386,plain,
    ( r2_hidden(k4_tarski(sK7,sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7))),sK9) = iProver_top
    | r2_hidden(k4_tarski(sK7,sK2(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8)) != iProver_top
    | v1_relat_1(k5_relat_1(sK9,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_1779,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7))),sK9)
    | k1_funct_1(sK9,sK7) = sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_1780,plain,
    ( k1_funct_1(sK9,sK7) = sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7))
    | r2_hidden(k4_tarski(sK7,sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7))),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1779])).

cnf(c_370,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1274,plain,
    ( X0 != X1
    | X0 = k1_funct_1(sK9,X2)
    | k1_funct_1(sK9,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_3258,plain,
    ( X0 != sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7))
    | X0 = k1_funct_1(sK9,sK7)
    | k1_funct_1(sK9,sK7) != sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_12735,plain,
    ( sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) != sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7))
    | sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) = k1_funct_1(sK9,sK7)
    | k1_funct_1(sK9,sK7) != sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) ),
    inference(instantiation,[status(thm)],[c_3258])).

cnf(c_369,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12736,plain,
    ( sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) = sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_18211,plain,
    ( sK6(sK9,sK8,sK7,sK2(k5_relat_1(sK9,sK8),sK7)) = k1_funct_1(sK9,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18031,c_22,c_24,c_1190,c_1334,c_1386,c_1780,c_9637,c_12735,c_12736,c_17955])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK6(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_752,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_844,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK6(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_752,c_750])).

cnf(c_4109,plain,
    ( r2_hidden(sK6(X0,X1,X2,X3),k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X3),k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_844,c_758])).

cnf(c_19135,plain,
    ( r2_hidden(k4_tarski(sK7,sK2(k5_relat_1(sK9,sK8),sK7)),k5_relat_1(sK9,sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_18211,c_4109])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8))
    | ~ r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8)))
    | ~ r2_hidden(sK7,k1_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,plain,
    ( r2_hidden(k1_funct_1(sK9,sK7),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(sK7,k1_relat_1(k5_relat_1(sK9,sK8))) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19135,c_17955,c_9637,c_1334,c_28,c_24,c_22])).


%------------------------------------------------------------------------------

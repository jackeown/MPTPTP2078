%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0716+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:58 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  117 (2498 expanded)
%              Number of clauses        :   67 ( 541 expanded)
%              Number of leaves         :   11 ( 653 expanded)
%              Depth                    :   26
%              Number of atoms          :  565 (18143 expanded)
%              Number of equality atoms :  186 (1211 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f34,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f53,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
            | ~ r1_tarski(X2,k1_relat_1(X0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
          & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
     => ( ( ~ r1_tarski(k9_relat_1(X0,sK6),k1_relat_1(X1))
          | ~ r1_tarski(sK6,k1_relat_1(X0))
          | ~ r1_tarski(sK6,k1_relat_1(k5_relat_1(X0,X1))) )
        & ( ( r1_tarski(k9_relat_1(X0,sK6),k1_relat_1(X1))
            & r1_tarski(sK6,k1_relat_1(X0)) )
          | r1_tarski(sK6,k1_relat_1(k5_relat_1(X0,X1))) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK5))
              | ~ r1_tarski(X2,k1_relat_1(X0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK5))) )
            & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(sK5))
                & r1_tarski(X2,k1_relat_1(X0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,sK5))) ) )
        & v1_funct_1(sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK4,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK4))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK4,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK4,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK4)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK4,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
      | ~ r1_tarski(sK6,k1_relat_1(sK4))
      | ~ r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) )
    & ( ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
        & r1_tarski(sK6,k1_relat_1(sK4)) )
      | r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) )
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f29,f28,f27])).

fof(f50,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
    | r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,
    ( r1_tarski(sK6,k1_relat_1(sK4))
    | r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
    | ~ r1_tarski(sK6,k1_relat_1(sK4))
    | ~ r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_616,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_620,plain,
    ( k1_funct_1(X0,sK2(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1407,plain,
    ( k1_funct_1(X0,sK2(X0,X1,sK3(k9_relat_1(X0,X1),X2))) = sK3(k9_relat_1(X0,X1),X2)
    | r1_tarski(k9_relat_1(X0,X1),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_620])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_621,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
    | r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_610,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) = iProver_top
    | r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_615,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_966,plain,
    ( r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,sK6)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_615])).

cnf(c_1922,plain,
    ( r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_966])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5)))
    | r1_tarski(sK6,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_609,plain,
    ( r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r1_tarski(sK6,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_967,plain,
    ( r1_tarski(sK6,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_615])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_612,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1108,plain,
    ( r1_tarski(sK6,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_612])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1219,plain,
    ( r1_tarski(sK6,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_21,c_22,c_23,c_24])).

cnf(c_1228,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1219,c_615])).

cnf(c_1952,plain,
    ( r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1922,c_21,c_22,c_1228])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_614,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) = iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2358,plain,
    ( r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_614])).

cnf(c_2939,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2358,c_21,c_22,c_23,c_24,c_1228])).

cnf(c_2940,plain,
    ( r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_2939])).

cnf(c_2948,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2940,c_615])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_617,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2952,plain,
    ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(sK3(X0,k1_relat_1(k5_relat_1(sK4,sK5))),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2948,c_617])).

cnf(c_3795,plain,
    ( r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_2952])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
    | ~ r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5)))
    | ~ r1_tarski(sK6,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_611,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) != iProver_top
    | r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) != iProver_top
    | r1_tarski(sK6,k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3985,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) != iProver_top
    | r1_tarski(sK6,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3795,c_611])).

cnf(c_27,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) != iProver_top
    | r1_tarski(sK6,k1_relat_1(k5_relat_1(sK4,sK5))) != iProver_top
    | r1_tarski(sK6,k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1232,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK3(X0,k1_relat_1(sK4)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_617])).

cnf(c_1319,plain,
    ( r1_tarski(sK6,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1232])).

cnf(c_3992,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3985,c_27,c_1319,c_3795])).

cnf(c_4483,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK6,sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)))) = sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_3992])).

cnf(c_852,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
    | r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k9_relat_1(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_856,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k9_relat_1(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_873,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k9_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK2(sK4,sK6,sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)))) = sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_880,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK6,sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)))) = sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
    | r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k9_relat_1(sK4,sK6)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_4842,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK6,sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)))) = sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4483,c_21,c_22,c_27,c_856,c_880,c_1319,c_3795])).

cnf(c_1961,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(sK4,sK5))) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X1),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_615])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_613,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2262,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(k1_funct_1(sK4,X1),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1961,c_613])).

cnf(c_2953,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2948,c_613])).

cnf(c_4127,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_21,c_22,c_23,c_24,c_2953])).

cnf(c_4128,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4127])).

cnf(c_4848,plain,
    ( r2_hidden(sK2(sK4,sK6,sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5))),sK6) != iProver_top
    | r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4842,c_4128])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_875,plain,
    ( r2_hidden(sK2(sK4,sK6,sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5))),sK6)
    | ~ r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k9_relat_1(sK4,sK6))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_876,plain,
    ( r2_hidden(sK2(sK4,sK6,sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5))),sK6) = iProver_top
    | r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k9_relat_1(sK4,sK6)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_853,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5))
    | ~ r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_854,plain,
    ( r1_tarski(k9_relat_1(sK4,sK6),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK3(k9_relat_1(sK4,sK6),k1_relat_1(sK5)),k1_relat_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4848,c_3795,c_1319,c_876,c_856,c_854,c_27,c_22,c_21])).


%------------------------------------------------------------------------------

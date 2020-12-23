%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0585+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 50.44s
% Output     : CNFRefutation 50.44s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 120 expanded)
%              Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  336 ( 842 expanded)
%              Number of equality atoms :   40 ( 106 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f641,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1284,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f1893,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1284])).

fof(f1894,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1893])).

fof(f1895,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1894])).

fof(f1896,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
          | ~ r2_hidden(sK127(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
            & r2_hidden(sK127(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1897,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK127(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
                    & r2_hidden(sK127(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK127,sK128])],[f1895,f1896])).

fof(f3002,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1897])).

fof(f4021,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3002])).

fof(f831,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1499,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f831])).

fof(f1985,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1499])).

fof(f1986,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1985])).

fof(f3266,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1986])).

fof(f3265,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1986])).

fof(f649,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1929,plain,(
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
    inference(nnf_transformation,[],[f649])).

fof(f1930,plain,(
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
    inference(rectify,[],[f1929])).

fof(f1933,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1932,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK145(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1931,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK144(X0,X1),X3),X0)
          | ~ r2_hidden(sK144(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK144(X0,X1),X4),X0)
          | r2_hidden(sK144(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1934,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK144(X0,X1),X3),X0)
            | ~ r2_hidden(sK144(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK144(X0,X1),sK145(X0,X1)),X0)
            | r2_hidden(sK144(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK144,sK145,sK146])],[f1930,f1933,f1932,f1931])).

fof(f3037,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1934])).

fof(f4035,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f3037])).

fof(f3005,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
      | ~ r2_hidden(sK127(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1897])).

fof(f3000,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1897])).

fof(f4023,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3000])).

fof(f3001,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1897])).

fof(f4022,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3001])).

fof(f661,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1298,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f661])).

fof(f3058,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1298])).

fof(f3004,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1897])).

fof(f3003,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK127(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1897])).

fof(f776,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f777,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f776])).

fof(f1432,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f777])).

fof(f1970,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
     => ( k7_relat_1(X0,k1_relat_1(sK161)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(sK161,k1_relat_1(X0))))
        & v1_relat_1(sK161) ) ) ),
    introduced(choice_axiom,[])).

fof(f1969,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k7_relat_1(sK160,k1_relat_1(X1)) != k7_relat_1(sK160,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK160))))
          & v1_relat_1(X1) )
      & v1_relat_1(sK160) ) ),
    introduced(choice_axiom,[])).

fof(f1971,plain,
    ( k7_relat_1(sK160,k1_relat_1(sK161)) != k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))
    & v1_relat_1(sK161)
    & v1_relat_1(sK160) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK160,sK161])],[f1432,f1970,f1969])).

fof(f3193,plain,(
    k7_relat_1(sK160,k1_relat_1(sK161)) != k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))) ),
    inference(cnf_transformation,[],[f1971])).

fof(f3192,plain,(
    v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f1971])).

fof(f3191,plain,(
    v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f1971])).

cnf(c_1001,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f4021])).

cnf(c_104306,plain,
    ( ~ r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),X0)
    | r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),k7_relat_1(sK160,X0))
    | ~ r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),sK160)
    | ~ v1_relat_1(k7_relat_1(sK160,X0))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_153561,plain,
    ( ~ r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))
    | r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),sK160)
    | ~ v1_relat_1(k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_104306])).

cnf(c_1262,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f3266])).

cnf(c_104174,plain,
    ( ~ r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),X0)
    | r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(k7_relat_1(sK161,X0)))
    | ~ r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(sK161))
    | ~ v1_relat_1(sK161) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_140162,plain,
    ( r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))
    | ~ r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(sK161))
    | ~ r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(sK160))
    | ~ v1_relat_1(sK161) ),
    inference(instantiation,[status(thm)],[c_104174])).

cnf(c_1263,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3265])).

cnf(c_126704,plain,
    ( ~ r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))
    | r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(sK161))
    | ~ v1_relat_1(sK161) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1036,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4035])).

cnf(c_104341,plain,
    ( r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(sK160))
    | ~ r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),sK160) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_998,plain,
    ( ~ r2_hidden(sK127(X0,X1,X2),X1)
    | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
    | ~ r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f3005])).

cnf(c_104165,plain,
    ( ~ r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(sK161))
    | ~ r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),sK160)
    | ~ v1_relat_1(k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(sK160)
    | k7_relat_1(sK160,k1_relat_1(sK161)) = k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_1003,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k7_relat_1(X3,X1)) ),
    inference(cnf_transformation,[],[f4023])).

cnf(c_94204,plain,
    ( r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))
    | ~ r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1002,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k7_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k7_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f4022])).

cnf(c_94201,plain,
    ( ~ r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),sK160)
    | ~ v1_relat_1(k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_1056,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3058])).

cnf(c_69255,plain,
    ( v1_relat_1(k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_999,plain,
    ( r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f3004])).

cnf(c_63155,plain,
    ( r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),sK160)
    | ~ v1_relat_1(k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(sK160)
    | k7_relat_1(sK160,k1_relat_1(sK161)) = k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_1000,plain,
    ( r2_hidden(sK127(X0,X1,X2),X1)
    | r2_hidden(k4_tarski(sK127(X0,X1,X2),sK128(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f3003])).

cnf(c_62133,plain,
    ( r2_hidden(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),k1_relat_1(sK161))
    | r2_hidden(k4_tarski(sK127(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160))))),sK128(sK160,k1_relat_1(sK161),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))),k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))))
    | ~ v1_relat_1(sK160)
    | k7_relat_1(sK160,k1_relat_1(sK161)) = k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_1189,negated_conjecture,
    ( k7_relat_1(sK160,k1_relat_1(sK161)) != k7_relat_1(sK160,k1_relat_1(k7_relat_1(sK161,k1_relat_1(sK160)))) ),
    inference(cnf_transformation,[],[f3193])).

cnf(c_1190,negated_conjecture,
    ( v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3192])).

cnf(c_1191,negated_conjecture,
    ( v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f3191])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_153561,c_140162,c_126704,c_104341,c_104165,c_94204,c_94201,c_69255,c_63155,c_62133,c_1189,c_1190,c_1191])).

%------------------------------------------------------------------------------

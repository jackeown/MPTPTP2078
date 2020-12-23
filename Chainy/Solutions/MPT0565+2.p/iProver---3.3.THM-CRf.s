%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0565+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 31.52s
% Output     : CNFRefutation 31.52s
% Verified   : 
% Statistics : Number of formulae       :   69 (  98 expanded)
%              Number of clauses        :   22 (  23 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  276 ( 424 expanded)
%              Number of equality atoms :   63 (  92 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f644,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1263,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f1856,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1263])).

fof(f1857,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1856])).

fof(f1860,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK136(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK136(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1859,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK135(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK135(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1858,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK134(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK134(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK134(X0,X1,X2),X5),X0) )
          | r2_hidden(sK134(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1861,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK134(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK134(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK135(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK134(X0,X1,X2),sK135(X0,X1,X2)),X0) )
                | r2_hidden(sK134(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK136(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK136(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK134,sK135,sK136])],[f1857,f1860,f1859,f1858])).

fof(f2963,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK134(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK134(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1861])).

fof(f649,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1881,plain,(
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
    inference(nnf_transformation,[],[f649])).

fof(f1882,plain,(
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
    inference(rectify,[],[f1881])).

fof(f1885,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK149(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1884,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK148(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1883,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK147(X0,X1)),X0)
          | ~ r2_hidden(sK147(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK147(X0,X1)),X0)
          | r2_hidden(sK147(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1886,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK147(X0,X1)),X0)
            | ~ r2_hidden(sK147(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK148(X0,X1),sK147(X0,X1)),X0)
            | r2_hidden(sK147(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK149(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK147,sK148,sK149])],[f1882,f1885,f1884,f1883])).

fof(f2979,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1886])).

fof(f3932,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f2979])).

fof(f409,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1035,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f409])).

fof(f2522,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f1035])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2083,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f3566,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1) ) ),
    inference(definition_unfolding,[],[f2522,f2083])).

fof(f648,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1875,plain,(
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
    inference(nnf_transformation,[],[f648])).

fof(f1876,plain,(
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
    inference(rectify,[],[f1875])).

fof(f1879,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1878,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK145(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1877,plain,(
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

fof(f1880,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK144,sK145,sK146])],[f1876,f1879,f1878,f1877])).

fof(f2975,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1880])).

fof(f3930,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2975])).

fof(f2974,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1880])).

fof(f3931,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2974])).

fof(f410,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1036,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f410])).

fof(f2523,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1036])).

fof(f3567,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f2523,f2083])).

fof(f2961,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK134(X0,X1,X2),sK135(X0,X1,X2)),X0)
      | r2_hidden(sK134(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1861])).

fof(f752,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f753,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(negated_conjecture,[],[f752])).

fof(f1379,plain,(
    ? [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) != k1_relat_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f753])).

fof(f1910,plain,
    ( ? [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) != k1_relat_1(X0)
        & v1_relat_1(X0) )
   => ( k10_relat_1(sK159,k2_relat_1(sK159)) != k1_relat_1(sK159)
      & v1_relat_1(sK159) ) ),
    introduced(choice_axiom,[])).

fof(f1911,plain,
    ( k10_relat_1(sK159,k2_relat_1(sK159)) != k1_relat_1(sK159)
    & v1_relat_1(sK159) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK159])],[f1379,f1910])).

fof(f3104,plain,(
    k10_relat_1(sK159,k2_relat_1(sK159)) != k1_relat_1(sK159) ),
    inference(cnf_transformation,[],[f1911])).

fof(f3103,plain,(
    v1_relat_1(sK159) ),
    inference(cnf_transformation,[],[f1911])).

cnf(c_1016,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK134(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(sK134(X2,X1,X3),X0),X2)
    | ~ v1_relat_1(X2)
    | k10_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f2963])).

cnf(c_48232,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK159))
    | ~ r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159))
    | ~ r2_hidden(k4_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),X0),sK159)
    | ~ v1_relat_1(sK159)
    | k10_relat_1(sK159,k2_relat_1(sK159)) = k1_relat_1(sK159) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_91666,plain,
    ( ~ r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159))
    | ~ r2_hidden(sK146(sK159,sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159))),k2_relat_1(sK159))
    | ~ r2_hidden(k4_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),sK146(sK159,sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)))),sK159)
    | ~ v1_relat_1(sK159)
    | k10_relat_1(sK159,k2_relat_1(sK159)) = k1_relat_1(sK159) ),
    inference(instantiation,[status(thm)],[c_48232])).

cnf(c_1038,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f3932])).

cnf(c_91656,plain,
    ( r2_hidden(sK146(sK159,sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159))),k2_relat_1(sK159))
    | ~ r2_hidden(k4_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),sK146(sK159,sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)))),sK159) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_582,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3566])).

cnf(c_91215,plain,
    ( r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159))
    | k4_xboole_0(k1_relat_1(sK159),k4_xboole_0(k1_relat_1(sK159),k1_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159))))) != k1_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159))) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1034,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3930])).

cnf(c_78379,plain,
    ( r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159))
    | ~ r2_hidden(k4_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),sK135(sK159,k2_relat_1(sK159),k1_relat_1(sK159))),sK159) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_78380,plain,
    ( r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159)) = iProver_top
    | r2_hidden(k4_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),sK135(sK159,k2_relat_1(sK159),k1_relat_1(sK159))),sK159) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78379])).

cnf(c_1035,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK146(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f3931])).

cnf(c_59481,plain,
    ( ~ r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159))
    | r2_hidden(k4_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),sK146(sK159,sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)))),sK159) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3567])).

cnf(c_59381,plain,
    ( ~ r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159))
    | k4_xboole_0(k1_relat_1(sK159),k4_xboole_0(k1_relat_1(sK159),k1_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159))))) = k1_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159))) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_59391,plain,
    ( k4_xboole_0(k1_relat_1(sK159),k4_xboole_0(k1_relat_1(sK159),k1_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159))))) = k1_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)))
    | r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59381])).

cnf(c_1018,plain,
    ( r2_hidden(sK134(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK134(X0,X1,X2),sK135(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f2961])).

cnf(c_48237,plain,
    ( r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159))
    | r2_hidden(k4_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),sK135(sK159,k2_relat_1(sK159),k1_relat_1(sK159))),sK159)
    | ~ v1_relat_1(sK159)
    | k10_relat_1(sK159,k2_relat_1(sK159)) = k1_relat_1(sK159) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_48238,plain,
    ( k10_relat_1(sK159,k2_relat_1(sK159)) = k1_relat_1(sK159)
    | r2_hidden(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),k1_relat_1(sK159)) = iProver_top
    | r2_hidden(k4_tarski(sK134(sK159,k2_relat_1(sK159),k1_relat_1(sK159)),sK135(sK159,k2_relat_1(sK159),k1_relat_1(sK159))),sK159) = iProver_top
    | v1_relat_1(sK159) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48237])).

cnf(c_1161,negated_conjecture,
    ( k10_relat_1(sK159,k2_relat_1(sK159)) != k1_relat_1(sK159) ),
    inference(cnf_transformation,[],[f3104])).

cnf(c_1162,negated_conjecture,
    ( v1_relat_1(sK159) ),
    inference(cnf_transformation,[],[f3103])).

cnf(c_1250,plain,
    ( v1_relat_1(sK159) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1162])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91666,c_91656,c_91215,c_78380,c_59481,c_59391,c_48238,c_1161,c_1250,c_1162])).

%------------------------------------------------------------------------------

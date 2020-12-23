%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0562+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 27.19s
% Output     : CNFRefutation 27.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 127 expanded)
%              Number of clauses        :   25 (  26 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  313 ( 773 expanded)
%              Number of equality atoms :   47 (  68 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1260,plain,(
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

fof(f1850,plain,(
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
    inference(nnf_transformation,[],[f1260])).

fof(f1851,plain,(
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
    inference(rectify,[],[f1850])).

fof(f1854,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK136(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK136(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1853,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK135(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK135(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1852,plain,(
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

fof(f1855,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK134,sK135,sK136])],[f1851,f1854,f1853,f1852])).

fof(f2954,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1855])).

fof(f3915,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2954])).

fof(f649,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1875,plain,(
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

fof(f1876,plain,(
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
    inference(rectify,[],[f1875])).

fof(f1879,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK149(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1878,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK148(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1877,plain,(
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

fof(f1880,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK147,sK148,sK149])],[f1876,f1879,f1878,f1877])).

fof(f2973,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1880])).

fof(f3922,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f2973])).

fof(f749,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f750,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k10_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f749])).

fof(f1373,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f1900,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) )
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) )
        | r2_hidden(X0,k10_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1373])).

fof(f1901,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) )
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) )
        | r2_hidden(X0,k10_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1900])).

fof(f1902,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) )
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X0,X4),X2)
            & r2_hidden(X4,k2_relat_1(X2)) )
        | r2_hidden(X0,k10_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(rectify,[],[f1901])).

fof(f1904,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK161,X1)
        & r2_hidden(k4_tarski(X0,sK161),X2)
        & r2_hidden(sK161,k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1903,plain,
    ( ? [X0,X1,X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | r2_hidden(X0,k10_relat_1(X2,X1)) )
        & v1_relat_1(X2) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK159)
            | ~ r2_hidden(k4_tarski(sK158,X3),sK160)
            | ~ r2_hidden(X3,k2_relat_1(sK160)) )
        | ~ r2_hidden(sK158,k10_relat_1(sK160,sK159)) )
      & ( ? [X4] :
            ( r2_hidden(X4,sK159)
            & r2_hidden(k4_tarski(sK158,X4),sK160)
            & r2_hidden(X4,k2_relat_1(sK160)) )
        | r2_hidden(sK158,k10_relat_1(sK160,sK159)) )
      & v1_relat_1(sK160) ) ),
    introduced(choice_axiom,[])).

fof(f1905,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(X3,sK159)
          | ~ r2_hidden(k4_tarski(sK158,X3),sK160)
          | ~ r2_hidden(X3,k2_relat_1(sK160)) )
      | ~ r2_hidden(sK158,k10_relat_1(sK160,sK159)) )
    & ( ( r2_hidden(sK161,sK159)
        & r2_hidden(k4_tarski(sK158,sK161),sK160)
        & r2_hidden(sK161,k2_relat_1(sK160)) )
      | r2_hidden(sK158,k10_relat_1(sK160,sK159)) )
    & v1_relat_1(sK160) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK158,sK159,sK160,sK161])],[f1902,f1904,f1903])).

fof(f3095,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK159)
      | ~ r2_hidden(k4_tarski(sK158,X3),sK160)
      | ~ r2_hidden(X3,k2_relat_1(sK160))
      | ~ r2_hidden(sK158,k10_relat_1(sK160,sK159)) ) ),
    inference(cnf_transformation,[],[f1905])).

fof(f424,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1651,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f424])).

fof(f2536,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f1651])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1929,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3569,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f2536,f1929])).

fof(f2952,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK136(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1855])).

fof(f3917,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK136(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2952])).

fof(f2953,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK136(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1855])).

fof(f3916,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK136(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2953])).

fof(f2537,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1651])).

fof(f3568,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f2537,f1929])).

fof(f3094,plain,
    ( r2_hidden(sK161,sK159)
    | r2_hidden(sK158,k10_relat_1(sK160,sK159)) ),
    inference(cnf_transformation,[],[f1905])).

fof(f3093,plain,
    ( r2_hidden(k4_tarski(sK158,sK161),sK160)
    | r2_hidden(sK158,k10_relat_1(sK160,sK159)) ),
    inference(cnf_transformation,[],[f1905])).

fof(f3091,plain,(
    v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f1905])).

cnf(c_1019,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f3915])).

cnf(c_66142,plain,
    ( ~ r2_hidden(k4_tarski(sK158,sK161),sK160)
    | ~ r2_hidden(sK161,X0)
    | r2_hidden(sK158,k10_relat_1(sK160,X0))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_100184,plain,
    ( ~ r2_hidden(k4_tarski(sK158,sK161),sK160)
    | ~ r2_hidden(sK161,sK159)
    | r2_hidden(sK158,k10_relat_1(sK160,sK159))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_66142])).

cnf(c_1038,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f3922])).

cnf(c_83634,plain,
    ( r2_hidden(sK136(sK160,sK159,sK158),k2_relat_1(sK160))
    | ~ r2_hidden(k4_tarski(sK158,sK136(sK160,sK159,sK158)),sK160) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_83635,plain,
    ( r2_hidden(sK136(sK160,sK159,sK158),k2_relat_1(sK160)) = iProver_top
    | r2_hidden(k4_tarski(sK158,sK136(sK160,sK159,sK158)),sK160) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83634])).

cnf(c_1155,negated_conjecture,
    ( ~ r2_hidden(X0,k2_relat_1(sK160))
    | ~ r2_hidden(X0,sK159)
    | ~ r2_hidden(k4_tarski(sK158,X0),sK160)
    | ~ r2_hidden(sK158,k10_relat_1(sK160,sK159)) ),
    inference(cnf_transformation,[],[f3095])).

cnf(c_83343,plain,
    ( ~ r2_hidden(sK136(sK160,sK159,sK158),k2_relat_1(sK160))
    | ~ r2_hidden(sK136(sK160,sK159,sK158),sK159)
    | ~ r2_hidden(k4_tarski(sK158,sK136(sK160,sK159,sK158)),sK160)
    | ~ r2_hidden(sK158,k10_relat_1(sK160,sK159)) ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_83344,plain,
    ( r2_hidden(sK136(sK160,sK159,sK158),k2_relat_1(sK160)) != iProver_top
    | r2_hidden(sK136(sK160,sK159,sK158),sK159) != iProver_top
    | r2_hidden(k4_tarski(sK158,sK136(sK160,sK159,sK158)),sK160) != iProver_top
    | r2_hidden(sK158,k10_relat_1(sK160,sK159)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83343])).

cnf(c_603,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3569])).

cnf(c_82503,plain,
    ( r2_hidden(sK158,k10_relat_1(sK160,sK159))
    | k4_xboole_0(k1_tarski(sK158),k10_relat_1(sK160,sK159)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_82504,plain,
    ( k4_xboole_0(k1_tarski(sK158),k10_relat_1(sK160,sK159)) != o_0_0_xboole_0
    | r2_hidden(sK158,k10_relat_1(sK160,sK159)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82503])).

cnf(c_1021,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK136(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3917])).

cnf(c_60134,plain,
    ( r2_hidden(k4_tarski(sK158,sK136(sK160,sK159,sK158)),sK160)
    | ~ r2_hidden(sK158,k10_relat_1(sK160,sK159))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_60135,plain,
    ( r2_hidden(k4_tarski(sK158,sK136(sK160,sK159,sK158)),sK160) = iProver_top
    | r2_hidden(sK158,k10_relat_1(sK160,sK159)) != iProver_top
    | v1_relat_1(sK160) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60134])).

cnf(c_1020,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK136(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3916])).

cnf(c_58719,plain,
    ( r2_hidden(sK136(sK160,sK159,sK158),sK159)
    | ~ r2_hidden(sK158,k10_relat_1(sK160,sK159))
    | ~ v1_relat_1(sK160) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_58720,plain,
    ( r2_hidden(sK136(sK160,sK159,sK158),sK159) = iProver_top
    | r2_hidden(sK158,k10_relat_1(sK160,sK159)) != iProver_top
    | v1_relat_1(sK160) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58719])).

cnf(c_602,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3568])).

cnf(c_55199,plain,
    ( ~ r2_hidden(sK158,k10_relat_1(sK160,sK159))
    | k4_xboole_0(k1_tarski(sK158),k10_relat_1(sK160,sK159)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_1156,negated_conjecture,
    ( r2_hidden(sK161,sK159)
    | r2_hidden(sK158,k10_relat_1(sK160,sK159)) ),
    inference(cnf_transformation,[],[f3094])).

cnf(c_1157,negated_conjecture,
    ( r2_hidden(k4_tarski(sK158,sK161),sK160)
    | r2_hidden(sK158,k10_relat_1(sK160,sK159)) ),
    inference(cnf_transformation,[],[f3093])).

cnf(c_1159,negated_conjecture,
    ( v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f3091])).

cnf(c_1247,plain,
    ( v1_relat_1(sK160) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_100184,c_83635,c_83344,c_82504,c_60135,c_58720,c_55199,c_1156,c_1157,c_1247,c_1159])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0541+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 27.64s
% Output     : CNFRefutation 27.64s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 343 expanded)
%              Number of clauses        :   36 (  75 expanded)
%              Number of leaves         :   13 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  336 (2145 expanded)
%              Number of equality atoms :   63 ( 175 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1232,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f1790,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1232])).

fof(f1791,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1790])).

fof(f1794,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK133(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK133(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1793,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK132(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK132(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1792,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK131(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK131(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK131(X0,X1,X2)),X0) )
          | r2_hidden(sK131(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1795,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK131(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK131(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK132(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK132(X0,X1,X2),sK131(X0,X1,X2)),X0) )
                | r2_hidden(sK131(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK133(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK133(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK131,sK132,sK133])],[f1791,f1794,f1793,f1792])).

fof(f2883,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1795])).

fof(f3801,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2883])).

fof(f720,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f721,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k9_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f720])).

fof(f1317,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f1835,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1317])).

fof(f1836,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1835])).

fof(f1837,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X4,X0),X2)
            & r2_hidden(X4,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(rectify,[],[f1836])).

fof(f1839,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK157,X1)
        & r2_hidden(k4_tarski(sK157,X0),X2)
        & r2_hidden(sK157,k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1838,plain,
    ( ? [X0,X1,X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | r2_hidden(X0,k9_relat_1(X2,X1)) )
        & v1_relat_1(X2) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK155)
            | ~ r2_hidden(k4_tarski(X3,sK154),sK156)
            | ~ r2_hidden(X3,k1_relat_1(sK156)) )
        | ~ r2_hidden(sK154,k9_relat_1(sK156,sK155)) )
      & ( ? [X4] :
            ( r2_hidden(X4,sK155)
            & r2_hidden(k4_tarski(X4,sK154),sK156)
            & r2_hidden(X4,k1_relat_1(sK156)) )
        | r2_hidden(sK154,k9_relat_1(sK156,sK155)) )
      & v1_relat_1(sK156) ) ),
    introduced(choice_axiom,[])).

fof(f1840,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(X3,sK155)
          | ~ r2_hidden(k4_tarski(X3,sK154),sK156)
          | ~ r2_hidden(X3,k1_relat_1(sK156)) )
      | ~ r2_hidden(sK154,k9_relat_1(sK156,sK155)) )
    & ( ( r2_hidden(sK157,sK155)
        & r2_hidden(k4_tarski(sK157,sK154),sK156)
        & r2_hidden(sK157,k1_relat_1(sK156)) )
      | r2_hidden(sK154,k9_relat_1(sK156,sK155)) )
    & v1_relat_1(sK156) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK154,sK155,sK156,sK157])],[f1837,f1839,f1838])).

fof(f2992,plain,
    ( r2_hidden(sK157,sK155)
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) ),
    inference(cnf_transformation,[],[f1840])).

fof(f2989,plain,(
    v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f1840])).

fof(f2882,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK133(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1795])).

fof(f3802,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK133(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2882])).

fof(f2881,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK133(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1795])).

fof(f3803,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK133(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2881])).

fof(f2993,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK155)
      | ~ r2_hidden(k4_tarski(X3,sK154),sK156)
      | ~ r2_hidden(X3,k1_relat_1(sK156))
      | ~ r2_hidden(sK154,k9_relat_1(sK156,sK155)) ) ),
    inference(cnf_transformation,[],[f1840])).

fof(f647,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1809,plain,(
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
    inference(nnf_transformation,[],[f647])).

fof(f1810,plain,(
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
    inference(rectify,[],[f1809])).

fof(f1813,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK143(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1812,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK142(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1811,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK141(X0,X1),X3),X0)
          | ~ r2_hidden(sK141(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK141(X0,X1),X4),X0)
          | r2_hidden(sK141(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1814,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK141(X0,X1),X3),X0)
            | ~ r2_hidden(sK141(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK141(X0,X1),sK142(X0,X1)),X0)
            | r2_hidden(sK141(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK143(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK141,sK142,sK143])],[f1810,f1813,f1812,f1811])).

fof(f2898,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1814])).

fof(f3806,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2898])).

fof(f2991,plain,
    ( r2_hidden(k4_tarski(sK157,sK154),sK156)
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) ),
    inference(cnf_transformation,[],[f1840])).

fof(f424,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1597,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f424])).

fof(f2471,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f1597])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1864,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3469,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f2471,f1864])).

fof(f2472,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1597])).

fof(f3468,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f2472,f1864])).

cnf(c_1013,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f3801])).

cnf(c_63974,plain,
    ( ~ r2_hidden(k4_tarski(sK157,sK154),sK156)
    | ~ r2_hidden(sK157,X0)
    | r2_hidden(sK154,k9_relat_1(sK156,X0))
    | ~ v1_relat_1(sK156) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_99714,plain,
    ( ~ r2_hidden(k4_tarski(sK157,sK154),sK156)
    | ~ r2_hidden(sK157,sK155)
    | r2_hidden(sK154,k9_relat_1(sK156,sK155))
    | ~ v1_relat_1(sK156) ),
    inference(instantiation,[status(thm)],[c_63974])).

cnf(c_1119,negated_conjecture,
    ( r2_hidden(sK157,sK155)
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) ),
    inference(cnf_transformation,[],[f2992])).

cnf(c_50960,plain,
    ( r2_hidden(sK157,sK155) = iProver_top
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_1122,negated_conjecture,
    ( v1_relat_1(sK156) ),
    inference(cnf_transformation,[],[f2989])).

cnf(c_1212,plain,
    ( v1_relat_1(sK156) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_1215,plain,
    ( r2_hidden(sK157,sK155) = iProver_top
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_1014,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK133(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3802])).

cnf(c_57246,plain,
    ( r2_hidden(sK133(sK156,sK155,sK154),sK155)
    | ~ r2_hidden(sK154,k9_relat_1(sK156,sK155))
    | ~ v1_relat_1(sK156) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_57247,plain,
    ( r2_hidden(sK133(sK156,sK155,sK154),sK155) = iProver_top
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) != iProver_top
    | v1_relat_1(sK156) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57246])).

cnf(c_1015,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK133(X1,X2,X0),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3803])).

cnf(c_58440,plain,
    ( r2_hidden(k4_tarski(sK133(sK156,sK155,sK154),sK154),sK156)
    | ~ r2_hidden(sK154,k9_relat_1(sK156,sK155))
    | ~ v1_relat_1(sK156) ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_58441,plain,
    ( r2_hidden(k4_tarski(sK133(sK156,sK155,sK154),sK154),sK156) = iProver_top
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) != iProver_top
    | v1_relat_1(sK156) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58440])).

cnf(c_1118,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK156))
    | ~ r2_hidden(X0,sK155)
    | ~ r2_hidden(k4_tarski(X0,sK154),sK156)
    | ~ r2_hidden(sK154,k9_relat_1(sK156,sK155)) ),
    inference(cnf_transformation,[],[f2993])).

cnf(c_80770,plain,
    ( ~ r2_hidden(sK133(sK156,sK155,sK154),k1_relat_1(sK156))
    | ~ r2_hidden(sK133(sK156,sK155,sK154),sK155)
    | ~ r2_hidden(k4_tarski(sK133(sK156,sK155,sK154),sK154),sK156)
    | ~ r2_hidden(sK154,k9_relat_1(sK156,sK155)) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_80771,plain,
    ( r2_hidden(sK133(sK156,sK155,sK154),k1_relat_1(sK156)) != iProver_top
    | r2_hidden(sK133(sK156,sK155,sK154),sK155) != iProver_top
    | r2_hidden(k4_tarski(sK133(sK156,sK155,sK154),sK154),sK156) != iProver_top
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80770])).

cnf(c_1028,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3806])).

cnf(c_81080,plain,
    ( r2_hidden(sK133(sK156,sK155,sK154),k1_relat_1(sK156))
    | ~ r2_hidden(k4_tarski(sK133(sK156,sK155,sK154),sK154),sK156) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_81081,plain,
    ( r2_hidden(sK133(sK156,sK155,sK154),k1_relat_1(sK156)) = iProver_top
    | r2_hidden(k4_tarski(sK133(sK156,sK155,sK154),sK154),sK156) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81080])).

cnf(c_81450,plain,
    ( r2_hidden(sK157,sK155) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50960,c_1212,c_1215,c_57247,c_58441,c_80771,c_81081])).

cnf(c_1120,negated_conjecture,
    ( r2_hidden(k4_tarski(sK157,sK154),sK156)
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) ),
    inference(cnf_transformation,[],[f2991])).

cnf(c_50959,plain,
    ( r2_hidden(k4_tarski(sK157,sK154),sK156) = iProver_top
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_1214,plain,
    ( r2_hidden(k4_tarski(sK157,sK154),sK156) = iProver_top
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_81154,plain,
    ( r2_hidden(k4_tarski(sK157,sK154),sK156) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50959,c_1212,c_1214,c_57247,c_58441,c_80771,c_81081])).

cnf(c_81156,plain,
    ( r2_hidden(k4_tarski(sK157,sK154),sK156) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_81154])).

cnf(c_603,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3469])).

cnf(c_79913,plain,
    ( r2_hidden(sK154,k9_relat_1(sK156,sK155))
    | k4_xboole_0(k1_tarski(sK154),k9_relat_1(sK156,sK155)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_79914,plain,
    ( k4_xboole_0(k1_tarski(sK154),k9_relat_1(sK156,sK155)) != o_0_0_xboole_0
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79913])).

cnf(c_64002,plain,
    ( ~ r2_hidden(k4_tarski(sK157,sK154),sK156)
    | r2_hidden(sK157,k1_relat_1(sK156)) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_64003,plain,
    ( r2_hidden(k4_tarski(sK157,sK154),sK156) != iProver_top
    | r2_hidden(sK157,k1_relat_1(sK156)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64002])).

cnf(c_63740,plain,
    ( ~ r2_hidden(k4_tarski(sK157,sK154),sK156)
    | ~ r2_hidden(sK157,k1_relat_1(sK156))
    | ~ r2_hidden(sK157,sK155)
    | ~ r2_hidden(sK154,k9_relat_1(sK156,sK155)) ),
    inference(instantiation,[status(thm)],[c_1118])).

cnf(c_63741,plain,
    ( r2_hidden(k4_tarski(sK157,sK154),sK156) != iProver_top
    | r2_hidden(sK157,k1_relat_1(sK156)) != iProver_top
    | r2_hidden(sK157,sK155) != iProver_top
    | r2_hidden(sK154,k9_relat_1(sK156,sK155)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63740])).

cnf(c_602,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3468])).

cnf(c_53822,plain,
    ( ~ r2_hidden(sK154,k9_relat_1(sK156,sK155))
    | k4_xboole_0(k1_tarski(sK154),k9_relat_1(sK156,sK155)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99714,c_81450,c_81156,c_81154,c_79914,c_64003,c_63741,c_53822,c_1119,c_1122])).

%------------------------------------------------------------------------------

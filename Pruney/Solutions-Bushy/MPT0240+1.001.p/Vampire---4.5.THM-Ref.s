%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0240+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:35 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 472 expanded)
%              Number of leaves         :    9 ( 138 expanded)
%              Depth                    :   23
%              Number of atoms          :  242 (2602 expanded)
%              Number of equality atoms :   83 (1110 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1898,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1897,f37])).

fof(f37,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1897,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f1889,f37])).

fof(f1889,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(equality_resolution,[],[f1860])).

fof(f1860,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK1,sK2)
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK1)) ) ),
    inference(subsumption_resolution,[],[f1859,f37])).

fof(f1859,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1,sK2),k1_tarski(k4_tarski(sK1,sK2)))
      | k4_tarski(X0,X1) != k4_tarski(sK1,sK2)
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK1)) ) ),
    inference(forward_demodulation,[],[f1833,f1816])).

fof(f1816,plain,(
    k4_tarski(sK1,sK2) = sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f1799,f38])).

fof(f38,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1799,plain,
    ( k4_tarski(sK1,sK2) = sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2)))
    | r2_hidden(sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(k4_tarski(sK1,sK2))) ),
    inference(backward_demodulation,[],[f1619,f1724])).

fof(f1724,plain,(
    sK2 = sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))) ),
    inference(resolution,[],[f1617,f38])).

fof(f1617,plain,(
    r2_hidden(sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f1616,f37])).

fof(f1616,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | r2_hidden(sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f1609,f37])).

fof(f1609,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | r2_hidden(sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK2)) ),
    inference(equality_resolution,[],[f368])).

fof(f368,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK1,sK2)
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK1))
      | r2_hidden(sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK2)) ) ),
    inference(subsumption_resolution,[],[f358,f37])).

fof(f358,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK1,sK2)
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK1))
      | ~ r2_hidden(k4_tarski(sK1,sK2),k1_tarski(k4_tarski(sK1,sK2)))
      | r2_hidden(sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK2)) ) ),
    inference(superposition,[],[f63,f163])).

fof(f163,plain,
    ( k4_tarski(sK1,sK2) = sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2)))
    | r2_hidden(sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK2)) ),
    inference(resolution,[],[f61,f38])).

fof(f61,plain,
    ( r2_hidden(sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(k4_tarski(sK1,sK2)))
    | r2_hidden(sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK2)) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
              & r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
                & r2_hidden(sK8(X0,X1,X8),X0)
                & r2_hidden(sK7(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X0)
        & r2_hidden(sK5(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X0)
        & r2_hidden(sK7(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f50,plain,(
    ~ sP0(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k1_tarski(k4_tarski(sK1,sK2)) != X0
      | ~ sP0(k1_tarski(sK2),k1_tarski(sK1),X0) ) ),
    inference(superposition,[],[f21,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f6])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f21,plain,(
    k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k4_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k4_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1))
   => k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(k4_tarski(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(k4_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2)))
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK1))
      | ~ r2_hidden(sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(k4_tarski(sK1,sK2))) ) ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( sP0(X0,X1,X2)
      | k4_tarski(X4,X5) != sK4(X0,X1,X2)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1619,plain,
    ( sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))) = k4_tarski(sK1,sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))))
    | r2_hidden(sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(k4_tarski(sK1,sK2))) ),
    inference(backward_demodulation,[],[f62,f1584])).

fof(f1584,plain,(
    sK1 = sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))) ),
    inference(resolution,[],[f1583,f38])).

fof(f1583,plain,(
    r2_hidden(sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f1582,f37])).

fof(f1582,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | r2_hidden(sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f1574,f37])).

fof(f1574,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | r2_hidden(sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK1)) ),
    inference(equality_resolution,[],[f347])).

fof(f347,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK1,sK2)
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK1))
      | r2_hidden(sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK1)) ) ),
    inference(subsumption_resolution,[],[f337,f37])).

fof(f337,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK1,sK2)
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK1))
      | ~ r2_hidden(k4_tarski(sK1,sK2),k1_tarski(k4_tarski(sK1,sK2)))
      | r2_hidden(sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK1)) ) ),
    inference(superposition,[],[f63,f147])).

fof(f147,plain,
    ( k4_tarski(sK1,sK2) = sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2)))
    | r2_hidden(sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK1)) ),
    inference(resolution,[],[f60,f38])).

fof(f60,plain,
    ( r2_hidden(sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(k4_tarski(sK1,sK2)))
    | r2_hidden(sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(sK1)) ),
    inference(resolution,[],[f50,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,
    ( sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))) = k4_tarski(sK5(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),sK6(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))))
    | r2_hidden(sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(k4_tarski(sK1,sK2))) ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1833,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK1,sK2)
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK1))
      | ~ r2_hidden(sK4(k1_tarski(sK2),k1_tarski(sK1),k1_tarski(k4_tarski(sK1,sK2))),k1_tarski(k4_tarski(sK1,sK2))) ) ),
    inference(backward_demodulation,[],[f63,f1816])).

%------------------------------------------------------------------------------

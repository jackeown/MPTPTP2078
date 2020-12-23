%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0217+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:17 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 133 expanded)
%              Number of leaves         :    7 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  175 ( 768 expanded)
%              Number of equality atoms :  123 ( 579 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1104,f943])).

fof(f943,plain,(
    sK3 != sK4 ),
    inference(superposition,[],[f496,f916])).

fof(f916,plain,(
    sK4 = sK6 ),
    inference(subsumption_resolution,[],[f912,f496])).

fof(f912,plain,
    ( sK3 = sK6
    | sK4 = sK6 ),
    inference(resolution,[],[f890,f838])).

fof(f838,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f574])).

fof(f574,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f423])).

fof(f423,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK9(X0,X1,X2) != X1
              & sK9(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sK9(X0,X1,X2) = X1
            | sK9(X0,X1,X2) = X0
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f421,f422])).

fof(f422,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK9(X0,X1,X2) != X1
            & sK9(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sK9(X0,X1,X2) = X1
          | sK9(X0,X1,X2) = X0
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f421,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f420])).

fof(f420,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f419])).

fof(f419,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f176])).

fof(f176,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f890,plain,(
    r2_hidden(sK6,k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f835,f494])).

fof(f494,plain,(
    k2_tarski(sK3,sK4) = k2_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f412])).

fof(f412,plain,
    ( sK3 != sK6
    & sK3 != sK5
    & k2_tarski(sK3,sK4) = k2_tarski(sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f302,f411])).

fof(f411,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) )
   => ( sK3 != sK6
      & sK3 != sK5
      & k2_tarski(sK3,sK4) = k2_tarski(sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f302,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f292])).

fof(f292,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(negated_conjecture,[],[f291])).

fof(f291,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(f835,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f834])).

fof(f834,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f576])).

fof(f576,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f423])).

fof(f496,plain,(
    sK3 != sK6 ),
    inference(cnf_transformation,[],[f412])).

fof(f1104,plain,(
    sK3 = sK4 ),
    inference(resolution,[],[f1074,f867])).

fof(f867,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f799])).

fof(f799,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f472])).

fof(f472,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK17(X0,X1) != X0
            | ~ r2_hidden(sK17(X0,X1),X1) )
          & ( sK17(X0,X1) = X0
            | r2_hidden(sK17(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f470,f471])).

fof(f471,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK17(X0,X1) != X0
          | ~ r2_hidden(sK17(X0,X1),X1) )
        & ( sK17(X0,X1) = X0
          | r2_hidden(sK17(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f470,plain,(
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
    inference(rectify,[],[f469])).

fof(f469,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1074,plain,(
    r2_hidden(sK3,k1_tarski(sK4)) ),
    inference(superposition,[],[f837,f1029])).

fof(f1029,plain,(
    k2_tarski(sK3,sK4) = k1_tarski(sK4) ),
    inference(forward_demodulation,[],[f1006,f594])).

fof(f594,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1006,plain,(
    k2_tarski(sK3,sK4) = k2_tarski(sK4,sK4) ),
    inference(backward_demodulation,[],[f917,f1003])).

fof(f1003,plain,(
    sK4 = sK5 ),
    inference(subsumption_resolution,[],[f999,f495])).

fof(f495,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f412])).

fof(f999,plain,
    ( sK3 = sK5
    | sK4 = sK5 ),
    inference(resolution,[],[f891,f838])).

fof(f891,plain,(
    r2_hidden(sK5,k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f837,f494])).

fof(f917,plain,(
    k2_tarski(sK3,sK4) = k2_tarski(sK5,sK4) ),
    inference(backward_demodulation,[],[f494,f916])).

fof(f837,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f836])).

fof(f836,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f575])).

fof(f575,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f423])).
%------------------------------------------------------------------------------

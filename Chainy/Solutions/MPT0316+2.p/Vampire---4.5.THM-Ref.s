%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0316+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 151 expanded)
%              Number of leaves         :    8 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  181 ( 541 expanded)
%              Number of equality atoms :   52 ( 189 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1423,plain,(
    $false ),
    inference(resolution,[],[f1422,f1339])).

fof(f1339,plain,(
    ! [X0] : sP10(X0,k2_tarski(X0,X0)) ),
    inference(equality_resolution,[],[f1213])).

fof(f1213,plain,(
    ! [X0,X1] :
      ( sP10(X0,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f883,f939])).

fof(f939,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f883,plain,(
    ! [X0,X1] :
      ( sP10(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f690])).

fof(f690,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP10(X0,X1) )
      & ( sP10(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f601])).

fof(f601,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP10(X0,X1) ) ),
    inference(definition_folding,[],[f175,f600])).

fof(f600,plain,(
    ! [X0,X1] :
      ( sP10(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1422,plain,(
    ! [X6] : ~ sP10(sK22,X6) ),
    inference(subsumption_resolution,[],[f1417,f1338])).

fof(f1338,plain,(
    ! [X3,X1] :
      ( ~ sP10(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f880])).

fof(f880,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP10(X0,X1) ) ),
    inference(cnf_transformation,[],[f689])).

fof(f689,plain,(
    ! [X0,X1] :
      ( ( sP10(X0,X1)
        | ( ( sK33(X0,X1) != X0
            | ~ r2_hidden(sK33(X0,X1),X1) )
          & ( sK33(X0,X1) = X0
            | r2_hidden(sK33(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP10(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33])],[f687,f688])).

fof(f688,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK33(X0,X1) != X0
          | ~ r2_hidden(sK33(X0,X1),X1) )
        & ( sK33(X0,X1) = X0
          | r2_hidden(sK33(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f687,plain,(
    ! [X0,X1] :
      ( ( sP10(X0,X1)
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
        | ~ sP10(X0,X1) ) ) ),
    inference(rectify,[],[f686])).

fof(f686,plain,(
    ! [X0,X1] :
      ( ( sP10(X0,X1)
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
        | ~ sP10(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f600])).

fof(f1417,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK22,X6)
      | ~ sP10(sK22,X6) ) ),
    inference(superposition,[],[f1413,f1212])).

fof(f1212,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | ~ sP10(X0,X1) ) ),
    inference(definition_unfolding,[],[f884,f939])).

fof(f884,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | ~ sP10(X0,X1) ) ),
    inference(cnf_transformation,[],[f690])).

fof(f1413,plain,(
    ~ r2_hidden(sK22,k2_tarski(sK22,sK22)) ),
    inference(subsumption_resolution,[],[f1403,f1369])).

fof(f1369,plain,(
    r2_hidden(sK23,sK25) ),
    inference(subsumption_resolution,[],[f1176,f957])).

fof(f957,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f719])).

fof(f719,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f718])).

fof(f718,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f313])).

fof(f313,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f1176,plain,
    ( r2_hidden(sK23,sK25)
    | r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k2_tarski(sK24,sK24),sK25)) ),
    inference(definition_unfolding,[],[f788,f939])).

fof(f788,plain,
    ( r2_hidden(sK23,sK25)
    | r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k1_tarski(sK24),sK25)) ),
    inference(cnf_transformation,[],[f624])).

fof(f624,plain,
    ( ( ~ r2_hidden(sK23,sK25)
      | sK22 != sK24
      | ~ r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k1_tarski(sK24),sK25)) )
    & ( ( r2_hidden(sK23,sK25)
        & sK22 = sK24 )
      | r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k1_tarski(sK24),sK25)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23,sK24,sK25])],[f622,f623])).

fof(f623,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK23,sK25)
        | sK22 != sK24
        | ~ r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k1_tarski(sK24),sK25)) )
      & ( ( r2_hidden(sK23,sK25)
          & sK22 = sK24 )
        | r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k1_tarski(sK24),sK25)) ) ) ),
    introduced(choice_axiom,[])).

fof(f622,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f621])).

fof(f621,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f426])).

fof(f426,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f339])).

fof(f339,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f338])).

fof(f338,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f1403,plain,
    ( ~ r2_hidden(sK23,sK25)
    | ~ r2_hidden(sK22,k2_tarski(sK22,sK22)) ),
    inference(resolution,[],[f1401,f958])).

fof(f958,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f719])).

fof(f1401,plain,(
    ~ r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k2_tarski(sK22,sK22),sK25)) ),
    inference(forward_demodulation,[],[f1400,f1399])).

fof(f1399,plain,(
    sK22 = sK24 ),
    inference(resolution,[],[f1398,f1339])).

fof(f1398,plain,(
    ! [X6] :
      ( ~ sP10(sK24,X6)
      | sK22 = sK24 ) ),
    inference(subsumption_resolution,[],[f1393,f879])).

fof(f879,plain,(
    ! [X0,X3,X1] :
      ( ~ sP10(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f689])).

fof(f1393,plain,(
    ! [X6] :
      ( r2_hidden(sK22,X6)
      | sK22 = sK24
      | ~ sP10(sK24,X6) ) ),
    inference(superposition,[],[f1373,f1212])).

fof(f1373,plain,
    ( r2_hidden(sK22,k2_tarski(sK24,sK24))
    | sK22 = sK24 ),
    inference(resolution,[],[f1177,f956])).

fof(f956,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f719])).

fof(f1177,plain,
    ( r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k2_tarski(sK24,sK24),sK25))
    | sK22 = sK24 ),
    inference(definition_unfolding,[],[f787,f939])).

fof(f787,plain,
    ( sK22 = sK24
    | r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k1_tarski(sK24),sK25)) ),
    inference(cnf_transformation,[],[f624])).

fof(f1400,plain,(
    ~ r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k2_tarski(sK24,sK24),sK25)) ),
    inference(global_subsumption,[],[f1399,f1368])).

fof(f1368,plain,
    ( sK22 != sK24
    | ~ r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k2_tarski(sK24,sK24),sK25)) ),
    inference(subsumption_resolution,[],[f1175,f954])).

fof(f954,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f717])).

fof(f717,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f716])).

fof(f716,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f319])).

fof(f319,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f1175,plain,
    ( ~ r2_hidden(sK23,sK25)
    | sK22 != sK24
    | ~ r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k2_tarski(sK24,sK24),sK25)) ),
    inference(definition_unfolding,[],[f789,f939])).

fof(f789,plain,
    ( ~ r2_hidden(sK23,sK25)
    | sK22 != sK24
    | ~ r2_hidden(k4_tarski(sK22,sK23),k2_zfmisc_1(k1_tarski(sK24),sK25)) ),
    inference(cnf_transformation,[],[f624])).
%------------------------------------------------------------------------------

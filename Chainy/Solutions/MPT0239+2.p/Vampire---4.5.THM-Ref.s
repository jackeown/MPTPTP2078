%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0239+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 124 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  185 ( 678 expanded)
%              Number of equality atoms :  108 ( 421 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f900,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f858,f858,f897,f581])).

fof(f581,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f494])).

fof(f494,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f493])).

fof(f493,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f306])).

fof(f306,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f897,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(trivial_inequality_removal,[],[f896])).

fof(f896,plain,
    ( sK0 != sK0
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(backward_demodulation,[],[f889,f895])).

fof(f895,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f890,f861])).

fof(f861,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f547])).

fof(f547,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f473])).

fof(f473,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK7(X0,X1,X2) != X1
              & sK7(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X1
            | sK7(X0,X1,X2) = X0
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f471,f472])).

fof(f472,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X1
            & sK7(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X1
          | sK7(X0,X1,X2) = X0
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f471,plain,(
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
    inference(rectify,[],[f470])).

fof(f470,plain,(
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
    inference(flattening,[],[f469])).

fof(f469,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f890,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k2_tarski(sK2,sK2)) ),
    inference(resolution,[],[f886,f579])).

fof(f579,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f494])).

fof(f886,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1)))
    | sK0 = sK2 ),
    inference(backward_demodulation,[],[f751,f885])).

fof(f885,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f881,f861])).

fof(f881,plain,
    ( sK1 = sK3
    | r2_hidden(sK1,k2_tarski(sK3,sK3)) ),
    inference(resolution,[],[f750,f580])).

fof(f580,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f494])).

fof(f750,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3)))
    | sK1 = sK3 ),
    inference(definition_unfolding,[],[f519,f654,f654])).

fof(f654,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f519,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f451])).

fof(f451,plain,
    ( ( sK1 != sK3
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f449,f450])).

fof(f450,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
        & ( ( X1 = X3
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f449,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f448])).

fof(f448,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f340])).

fof(f340,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f332])).

fof(f332,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f331])).

fof(f331,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f751,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f518,f654,f654])).

fof(f518,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f451])).

fof(f889,plain,
    ( sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(trivial_inequality_removal,[],[f888])).

fof(f888,plain,
    ( sK1 != sK1
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(backward_demodulation,[],[f879,f885])).

fof(f879,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(inner_rewriting,[],[f878])).

fof(f878,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1))) ),
    inference(inner_rewriting,[],[f749])).

fof(f749,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f520,f654,f654])).

fof(f520,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f451])).

fof(f858,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f857])).

fof(f857,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f549])).

fof(f549,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f473])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0222+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:17 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 (  93 expanded)
%              Number of equality atoms :   35 (  43 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1519,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1492,f1283])).

fof(f1283,plain,(
    ~ sQ31_eqProxy(sK5,sK4) ),
    inference(resolution,[],[f1020,f1239])).

fof(f1239,plain,(
    ! [X0,X1] :
      ( ~ sQ31_eqProxy(X0,X1)
      | sQ31_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f1004])).

fof(f1004,plain,(
    ! [X1,X0] :
      ( sQ31_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ31_eqProxy])])).

fof(f1020,plain,(
    ~ sQ31_eqProxy(sK4,sK5) ),
    inference(equality_proxy_replacement,[],[f544,f1004])).

fof(f544,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f441])).

fof(f441,plain,
    ( ~ r1_xboole_0(k1_tarski(sK4),k1_tarski(sK5))
    & sK4 != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f313,f440])).

fof(f440,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( ~ r1_xboole_0(k1_tarski(sK4),k1_tarski(sK5))
      & sK4 != sK5 ) ),
    introduced(choice_axiom,[])).

fof(f313,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f301])).

fof(f301,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f300])).

fof(f300,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f1492,plain,(
    sQ31_eqProxy(sK5,sK4) ),
    inference(resolution,[],[f1332,f1093])).

fof(f1093,plain,(
    ! [X0,X3] :
      ( sQ31_eqProxy(X0,X3)
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_proxy_replacement,[],[f955,f1004])).

fof(f955,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f676])).

fof(f676,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f480])).

fof(f480,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK16(X0,X1) != X0
            | ~ r2_hidden(sK16(X0,X1),X1) )
          & ( sK16(X0,X1) = X0
            | r2_hidden(sK16(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f478,f479])).

fof(f479,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK16(X0,X1) != X0
          | ~ r2_hidden(sK16(X0,X1),X1) )
        & ( sK16(X0,X1) = X0
          | r2_hidden(sK16(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f478,plain,(
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
    inference(rectify,[],[f477])).

fof(f477,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1332,plain,(
    r2_hidden(sK4,k1_tarski(sK5)) ),
    inference(resolution,[],[f545,f632])).

fof(f632,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f326])).

fof(f326,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f293])).

fof(f293,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f545,plain,(
    ~ r1_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f441])).
%------------------------------------------------------------------------------

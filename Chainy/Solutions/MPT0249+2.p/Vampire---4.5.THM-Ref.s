%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0249+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   24 (  62 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 197 expanded)
%              Number of equality atoms :   70 ( 196 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1473,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1472,f530])).

fof(f530,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f460])).

fof(f460,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f354,f459])).

fof(f459,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f354,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f346])).

fof(f346,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f345])).

fof(f345,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f1472,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1360,f1361])).

fof(f1361,plain,(
    sK1 = k2_tarski(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f531,f769,f928])).

fof(f928,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) != k2_tarski(X0,X0)
      | k1_xboole_0 = X1
      | k2_tarski(X0,X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f777])).

fof(f777,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | k1_xboole_0 = X1
      | k2_tarski(X0,X0) = X1
      | k2_xboole_0(X1,X2) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f533,f621,f621,f621])).

fof(f621,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f533,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f355])).

fof(f355,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f344])).

fof(f344,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f769,plain,(
    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f529,f621])).

fof(f529,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f460])).

fof(f531,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f460])).

fof(f1360,plain,(
    sK2 = k2_tarski(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f532,f769,f925])).

fof(f925,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) != k2_tarski(X0,X0)
      | k2_tarski(X0,X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f770])).

fof(f770,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k2_tarski(X0,X0) = X2
      | k2_tarski(X0,X0) = X2
      | k2_xboole_0(X1,X2) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f540,f621,f621,f621])).

fof(f540,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f355])).

fof(f532,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f460])).
%------------------------------------------------------------------------------

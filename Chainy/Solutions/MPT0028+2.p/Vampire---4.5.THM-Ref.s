%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0028+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  55 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 167 expanded)
%              Number of equality atoms :   18 (  36 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(subsumption_resolution,[],[f239,f241])).

fof(f241,plain,(
    ~ r1_tarski(sK9(sK6,k2_xboole_0(sK6,sK7),sK6),sK6) ),
    inference(unit_resulting_resolution,[],[f231,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK9(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_tarski(sK9(X0,X1,X2),X0)
        & r1_tarski(sK9(X0,X1,X2),X1)
        & r1_tarski(sK9(X0,X1,X2),X2) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f120,f121])).

fof(f121,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X1)
          & r1_tarski(X3,X2) )
     => ( ~ r1_tarski(sK9(X0,X1,X2),X0)
        & r1_tarski(sK9(X0,X1,X2),X1)
        & r1_tarski(sK9(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f120,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X1)
          & r1_tarski(X3,X2) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f119])).

fof(f119,plain,(
    ! [X0,X2,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X2,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f231,plain,(
    sP2(sK6,k2_xboole_0(sK6,sK7),sK6) ),
    inference(unit_resulting_resolution,[],[f229,f189,f154,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | sP2(X0,X2,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | sP2(X0,X2,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_folding,[],[f71,f102])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f154,plain,(
    sK6 != k3_xboole_0(sK6,k2_xboole_0(sK6,sK7)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    sK6 != k3_xboole_0(sK6,k2_xboole_0(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f69,f109])).

fof(f109,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) != X0
   => sK6 != k3_xboole_0(sK6,k2_xboole_0(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ? [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f54])).

fof(f54,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f53])).

fof(f53,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f189,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f229,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f239,plain,(
    r1_tarski(sK9(sK6,k2_xboole_0(sK6,sK7),sK6),sK6) ),
    inference(unit_resulting_resolution,[],[f231,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK9(X0,X1,X2),X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f122])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0007+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  24 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f73])).

fof(f73,plain,(
    ! [X1] : ~ r2_hidden(X1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 )
   => ( ! [X1] : ~ r2_hidden(X1,sK0)
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] : ~ r2_hidden(X1,X0)
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f107,plain,(
    r2_hidden(sK7(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f106,f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f69,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f106,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f72,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f72,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------

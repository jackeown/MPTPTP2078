%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0055+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 181 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  250 (1080 expanded)
%              Number of equality atoms :   32 ( 165 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3065,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f625,f2548,f2564,f3064])).

fof(f3064,plain,
    ( ~ spl18_1
    | spl18_2 ),
    inference(avatar_contradiction_clause,[],[f3063])).

fof(f3063,plain,
    ( $false
    | ~ spl18_1
    | spl18_2 ),
    inference(subsumption_resolution,[],[f3062,f440])).

fof(f440,plain,(
    r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f426,f347])).

fof(f347,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f311])).

fof(f311,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f193])).

fof(f193,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK12(X0,X1,X2),X1)
            | ~ r2_hidden(sK12(X0,X1,X2),X0)
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
              & r2_hidden(sK12(X0,X1,X2),X0) )
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f191,f192])).

fof(f192,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK12(X0,X1,X2),X1)
          | ~ r2_hidden(sK12(X0,X1,X2),X0)
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
            & r2_hidden(sK12(X0,X1,X2),X0) )
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f191,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f190])).

fof(f190,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f189])).

fof(f189,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f426,plain,
    ( r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK0)
    | r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f357,f419])).

fof(f419,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f320,f354])).

fof(f354,plain,(
    ! [X1,X0] :
      ( sQ17_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ17_eqProxy])])).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f198])).

fof(f198,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
            | ~ r2_hidden(sK13(X0,X1,X2),X0)
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK13(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f196,f197])).

fof(f197,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
          | ~ r2_hidden(sK13(X0,X1,X2),X0)
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(sK13(X0,X1,X2),X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f196,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f195])).

fof(f195,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f194])).

fof(f194,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f357,plain,(
    ~ sQ17_eqProxy(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f209,f354])).

fof(f209,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f155])).

fof(f155,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f102,f154])).

fof(f154,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f85])).

fof(f85,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3062,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK0)
    | ~ spl18_1
    | spl18_2 ),
    inference(subsumption_resolution,[],[f3048,f447])).

fof(f447,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK1)
    | spl18_2 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl18_2
  <=> r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f3048,plain,
    ( r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK0)
    | ~ spl18_1 ),
    inference(resolution,[],[f2567,f345])).

fof(f345,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f313])).

fof(f313,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f193])).

fof(f2567,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | ~ spl18_1 ),
    inference(resolution,[],[f444,f346])).

fof(f346,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f312])).

fof(f312,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f193])).

fof(f444,plain,
    ( r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl18_1 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl18_1
  <=> r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f2564,plain,
    ( spl18_1
    | spl18_2 ),
    inference(avatar_split_clause,[],[f2563,f446,f442])).

fof(f2563,plain,
    ( r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl18_2 ),
    inference(subsumption_resolution,[],[f2549,f357])).

fof(f2549,plain,
    ( sQ17_eqProxy(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl18_2 ),
    inference(resolution,[],[f447,f418])).

fof(f418,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f321,f354])).

fof(f321,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f198])).

fof(f2548,plain,
    ( spl18_1
    | ~ spl18_2 ),
    inference(avatar_contradiction_clause,[],[f2547])).

fof(f2547,plain,
    ( $false
    | spl18_1
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f756,f618])).

fof(f618,plain,
    ( ! [X10] : ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(X10,sK1))
    | ~ spl18_2 ),
    inference(resolution,[],[f448,f346])).

fof(f448,plain,
    ( r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK1)
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f446])).

fof(f756,plain,
    ( r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | spl18_1 ),
    inference(subsumption_resolution,[],[f740,f440])).

fof(f740,plain,
    ( r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK0)
    | spl18_1 ),
    inference(resolution,[],[f443,f345])).

fof(f443,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl18_1 ),
    inference(avatar_component_clause,[],[f442])).

fof(f625,plain,
    ( ~ spl18_1
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f624,f446,f442])).

fof(f624,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f623,f440])).

fof(f623,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f603,f357])).

fof(f603,plain,
    ( sQ17_eqProxy(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK13(sK0,sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl18_2 ),
    inference(resolution,[],[f448,f417])).

fof(f417,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k3_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f322,f354])).

fof(f322,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f198])).
%------------------------------------------------------------------------------

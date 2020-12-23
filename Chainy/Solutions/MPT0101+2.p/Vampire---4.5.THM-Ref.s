%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0101+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:09 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 218 expanded)
%              Number of leaves         :   15 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  404 ( 986 expanded)
%              Number of equality atoms :   39 ( 105 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3765,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3585,f3586,f3606,f3627,f3628,f3631,f3659,f3661,f3689,f3690,f3691,f3760,f3764])).

fof(f3764,plain,
    ( spl19_149
    | ~ spl19_18 ),
    inference(avatar_split_clause,[],[f3736,f723,f3557])).

fof(f3557,plain,
    ( spl19_149
  <=> r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_149])])).

fof(f723,plain,
    ( spl19_18
  <=> r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_18])])).

fof(f3736,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl19_18 ),
    inference(resolution,[],[f725,f495])).

fof(f495,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f453])).

fof(f453,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f286])).

fof(f286,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
            | ~ r2_hidden(sK12(X0,X1,X2),X0)
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK12(X0,X1,X2),X1)
              & r2_hidden(sK12(X0,X1,X2),X0) )
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f284,f285])).

fof(f285,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
          | ~ r2_hidden(sK12(X0,X1,X2),X0)
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK12(X0,X1,X2),X1)
            & r2_hidden(sK12(X0,X1,X2),X0) )
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f284,plain,(
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
    inference(rectify,[],[f283])).

fof(f283,plain,(
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
    inference(flattening,[],[f282])).

fof(f282,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f725,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl19_18 ),
    inference(avatar_component_clause,[],[f723])).

fof(f3760,plain,
    ( spl19_150
    | ~ spl19_18 ),
    inference(avatar_split_clause,[],[f3737,f723,f3561])).

fof(f3561,plain,
    ( spl19_150
  <=> r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_150])])).

fof(f3737,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ spl19_18 ),
    inference(resolution,[],[f725,f494])).

fof(f494,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f454])).

fof(f454,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f286])).

fof(f3691,plain,
    ( ~ spl19_149
    | ~ spl19_150
    | ~ spl19_17 ),
    inference(avatar_split_clause,[],[f3667,f719,f3561,f3557])).

fof(f719,plain,
    ( spl19_17
  <=> r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_17])])).

fof(f3667,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl19_17 ),
    inference(resolution,[],[f720,f472])).

fof(f472,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f297])).

fof(f297,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f231])).

fof(f231,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f720,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | ~ spl19_17 ),
    inference(avatar_component_clause,[],[f719])).

fof(f3690,plain,
    ( spl19_149
    | spl19_150
    | ~ spl19_17 ),
    inference(avatar_split_clause,[],[f3666,f719,f3561,f3557])).

fof(f3666,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl19_17 ),
    inference(resolution,[],[f720,f471])).

fof(f471,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f297])).

fof(f3689,plain,
    ( spl19_18
    | ~ spl19_16
    | ~ spl19_17 ),
    inference(avatar_split_clause,[],[f3688,f719,f715,f723])).

fof(f715,plain,
    ( spl19_16
  <=> r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_16])])).

fof(f3688,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl19_16
    | ~ spl19_17 ),
    inference(subsumption_resolution,[],[f3687,f716])).

fof(f716,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | ~ spl19_16 ),
    inference(avatar_component_clause,[],[f715])).

fof(f3687,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | ~ spl19_17 ),
    inference(subsumption_resolution,[],[f3664,f613])).

fof(f613,plain,(
    ~ sQ18_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f508,f597])).

fof(f597,plain,(
    ! [X0,X1] :
      ( ~ sQ18_eqProxy(X0,X1)
      | sQ18_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f504])).

fof(f504,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f508,plain,(
    ~ sQ18_eqProxy(k2_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f302,f504])).

fof(f302,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f247])).

fof(f247,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f152,f246])).

fof(f246,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f152,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f145])).

fof(f145,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f144])).

fof(f144,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f3664,plain,
    ( sQ18_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | ~ spl19_17 ),
    inference(resolution,[],[f720,f585])).

fof(f585,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f449,f504])).

fof(f449,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f281])).

fof(f281,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ( ( ( ( ~ r2_hidden(sK11(X0,X1,X2),X2)
              | ~ r2_hidden(sK11(X0,X1,X2),X1) )
            & ( r2_hidden(sK11(X0,X1,X2),X2)
              | r2_hidden(sK11(X0,X1,X2),X1) ) )
          | r2_hidden(sK11(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK11(X0,X1,X2),X1)
              | ~ r2_hidden(sK11(X0,X1,X2),X2) )
            & ( r2_hidden(sK11(X0,X1,X2),X2)
              | ~ r2_hidden(sK11(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f279,f280])).

fof(f280,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ r2_hidden(X3,X0) ) )
     => ( ( ( ( ~ r2_hidden(sK11(X0,X1,X2),X2)
              | ~ r2_hidden(sK11(X0,X1,X2),X1) )
            & ( r2_hidden(sK11(X0,X1,X2),X2)
              | r2_hidden(sK11(X0,X1,X2),X1) ) )
          | r2_hidden(sK11(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK11(X0,X1,X2),X1)
              | ~ r2_hidden(sK11(X0,X1,X2),X2) )
            & ( r2_hidden(sK11(X0,X1,X2),X2)
              | ~ r2_hidden(sK11(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f279,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f230])).

fof(f230,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r2_hidden(X3,X0)
        <~> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f3661,plain,
    ( spl19_149
    | spl19_150
    | ~ spl19_16 ),
    inference(avatar_split_clause,[],[f3636,f715,f3561,f3557])).

fof(f3636,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl19_16 ),
    inference(resolution,[],[f716,f501])).

fof(f501,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f465])).

fof(f465,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f296])).

fof(f296,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
              & ~ r2_hidden(sK14(X0,X1,X2),X0) )
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( r2_hidden(sK14(X0,X1,X2),X1)
            | r2_hidden(sK14(X0,X1,X2),X0)
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f294,f295])).

fof(f295,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            & ~ r2_hidden(sK14(X0,X1,X2),X0) )
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( r2_hidden(sK14(X0,X1,X2),X1)
          | r2_hidden(sK14(X0,X1,X2),X0)
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f294,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f293])).

fof(f293,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f292])).

fof(f292,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f3659,plain,
    ( ~ spl19_18
    | spl19_17
    | ~ spl19_16 ),
    inference(avatar_split_clause,[],[f3658,f715,f719,f723])).

fof(f3658,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl19_16 ),
    inference(subsumption_resolution,[],[f3633,f613])).

fof(f3633,plain,
    ( sQ18_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl19_16 ),
    inference(resolution,[],[f716,f584])).

fof(f584,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f450,f504])).

fof(f450,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f281])).

fof(f3631,plain,
    ( spl19_18
    | spl19_16
    | spl19_17 ),
    inference(avatar_split_clause,[],[f3630,f719,f715,f723])).

fof(f3630,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl19_16
    | spl19_17 ),
    inference(subsumption_resolution,[],[f3629,f721])).

fof(f721,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl19_17 ),
    inference(avatar_component_clause,[],[f719])).

fof(f3629,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl19_16 ),
    inference(subsumption_resolution,[],[f3612,f613])).

fof(f3612,plain,
    ( sQ18_eqProxy(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl19_16 ),
    inference(resolution,[],[f717,f583])).

fof(f583,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k5_xboole_0(X1,X2),X0)
      | r2_hidden(sK11(X0,X1,X2),X2)
      | r2_hidden(sK11(X0,X1,X2),X1)
      | r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(equality_proxy_replacement,[],[f451,f504])).

fof(f451,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,X2) = X0
      | r2_hidden(sK11(X0,X1,X2),X2)
      | r2_hidden(sK11(X0,X1,X2),X1)
      | r2_hidden(sK11(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f281])).

fof(f717,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | spl19_16 ),
    inference(avatar_component_clause,[],[f715])).

fof(f3628,plain,
    ( ~ spl19_150
    | spl19_16 ),
    inference(avatar_split_clause,[],[f3611,f715,f3561])).

fof(f3611,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | spl19_16 ),
    inference(resolution,[],[f717,f499])).

fof(f499,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f467])).

fof(f467,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f296])).

fof(f3627,plain,
    ( ~ spl19_149
    | spl19_16 ),
    inference(avatar_split_clause,[],[f3610,f715,f3557])).

fof(f3610,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl19_16 ),
    inference(resolution,[],[f717,f500])).

fof(f500,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f466])).

fof(f466,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f296])).

fof(f3606,plain,
    ( ~ spl19_149
    | ~ spl19_150
    | spl19_18 ),
    inference(avatar_split_clause,[],[f3590,f723,f3561,f3557])).

fof(f3590,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl19_18 ),
    inference(resolution,[],[f724,f493])).

fof(f493,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f455])).

fof(f455,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f286])).

fof(f724,plain,
    ( ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl19_18 ),
    inference(avatar_component_clause,[],[f723])).

fof(f3586,plain,
    ( ~ spl19_150
    | spl19_149
    | spl19_17 ),
    inference(avatar_split_clause,[],[f3569,f719,f3557,f3561])).

fof(f3569,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | spl19_17 ),
    inference(resolution,[],[f721,f474])).

fof(f474,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f297])).

fof(f3585,plain,
    ( ~ spl19_149
    | spl19_150
    | spl19_17 ),
    inference(avatar_split_clause,[],[f3568,f719,f3561,f3557])).

fof(f3568,plain,
    ( r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK11(k2_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl19_17 ),
    inference(resolution,[],[f721,f473])).

fof(f473,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f297])).
%------------------------------------------------------------------------------

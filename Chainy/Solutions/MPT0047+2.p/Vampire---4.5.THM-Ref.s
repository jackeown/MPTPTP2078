%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0047+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 121 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  292 ( 620 expanded)
%              Number of equality atoms :   37 (  87 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f472,f1053,f1059,f1109,f1185])).

fof(f1185,plain,
    ( spl11_7
    | ~ spl11_8
    | spl11_11 ),
    inference(avatar_contradiction_clause,[],[f1184])).

fof(f1184,plain,
    ( $false
    | spl11_7
    | ~ spl11_8
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1183,f471])).

fof(f471,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl11_8
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f1183,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | spl11_7
    | spl11_11 ),
    inference(forward_demodulation,[],[f1182,f178])).

fof(f178,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1182,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK1,sK0))
    | spl11_7
    | spl11_11 ),
    inference(forward_demodulation,[],[f1156,f217])).

fof(f217,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1156,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | spl11_7
    | spl11_11 ),
    inference(unit_resulting_resolution,[],[f532,f466,f260])).

fof(f260,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f181])).

fof(f181,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f139])).

fof(f139,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f137,f138])).

fof(f138,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f137,plain,(
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
    inference(rectify,[],[f136])).

fof(f136,plain,(
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
    inference(flattening,[],[f135])).

fof(f135,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f466,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl11_7 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl11_7
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f532,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),sK1)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f531])).

fof(f531,plain,
    ( spl11_11
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f1109,plain,
    ( spl11_7
    | ~ spl11_11 ),
    inference(avatar_contradiction_clause,[],[f1108])).

fof(f1108,plain,
    ( $false
    | spl11_7
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f1081,f466])).

fof(f1081,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl11_11 ),
    inference(unit_resulting_resolution,[],[f167,f533,f207])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f144,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f142,f143])).

fof(f143,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f142,plain,(
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
    inference(rectify,[],[f141])).

fof(f141,plain,(
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
    inference(flattening,[],[f140])).

fof(f140,plain,(
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

fof(f533,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),sK1)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f531])).

fof(f167,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f91,f129])).

fof(f129,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1)
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f78])).

fof(f78,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f77])).

fof(f77,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1059,plain,
    ( ~ spl11_7
    | ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f1058])).

fof(f1058,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f471,f1055])).

fof(f1055,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1054,f467])).

fof(f467,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f465])).

fof(f1054,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f771,f985])).

fof(f985,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),sK1)
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f467,f262])).

fof(f262,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f204])).

fof(f204,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f144])).

fof(f771,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f280])).

fof(f280,plain,(
    ! [X2] :
      ( k4_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,X2),sK1)
      | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,X2),k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,X2),X2) ) ),
    inference(superposition,[],[f167,f208])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f1053,plain,
    ( ~ spl11_7
    | spl11_8 ),
    inference(avatar_contradiction_clause,[],[f1052])).

fof(f1052,plain,
    ( $false
    | ~ spl11_7
    | spl11_8 ),
    inference(subsumption_resolution,[],[f1014,f987])).

fof(f987,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),sK0)
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f218,f467,f240])).

fof(f240,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f155,f156])).

fof(f156,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f218,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1014,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),sK0)
    | spl11_8 ),
    inference(unit_resulting_resolution,[],[f470,f259])).

fof(f259,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f182])).

fof(f182,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f139])).

fof(f470,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | spl11_8 ),
    inference(avatar_component_clause,[],[f469])).

fof(f472,plain,
    ( spl11_7
    | spl11_8 ),
    inference(avatar_split_clause,[],[f463,f469,f465])).

fof(f463,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f278])).

fof(f278,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,X0),k2_xboole_0(sK0,sK1))
      | r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK1,X0),X0) ) ),
    inference(superposition,[],[f167,f206])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f144])).
%------------------------------------------------------------------------------

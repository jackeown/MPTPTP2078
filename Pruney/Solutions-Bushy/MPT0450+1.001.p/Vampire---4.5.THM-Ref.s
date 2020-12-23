%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0450+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:00 EST 2020

% Result     : Theorem 41.97s
% Output     : Refutation 41.97s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 401 expanded)
%              Number of leaves         :   33 ( 149 expanded)
%              Depth                    :   12
%              Number of atoms          :  502 (1734 expanded)
%              Number of equality atoms :   34 ( 126 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f118,f157,f175,f176,f191,f196,f557,f3348,f3459,f3462,f3539,f3597,f3614,f3753,f9260,f51316,f51685,f58961,f59297])).

fof(f59297,plain,
    ( ~ spl5_415
    | ~ spl5_9
    | spl5_45 ),
    inference(avatar_split_clause,[],[f59153,f3093,f150,f9257])).

fof(f9257,plain,
    ( spl5_415
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_415])])).

fof(f150,plain,
    ( spl5_9
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f3093,plain,
    ( spl5_45
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f59153,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_9
    | spl5_45 ),
    inference(unit_resulting_resolution,[],[f4381,f379])).

fof(f379,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k3_xboole_0(sK0,sK1)))
        | r2_hidden(X0,k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) )
    | ~ spl5_9 ),
    inference(resolution,[],[f152,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f152,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f4381,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_xboole_0(X0,k2_relat_1(sK1)))
    | spl5_45 ),
    inference(unit_resulting_resolution,[],[f3094,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f3094,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(sK1))
    | spl5_45 ),
    inference(avatar_component_clause,[],[f3093])).

fof(f58961,plain,
    ( ~ spl5_414
    | ~ spl5_11
    | spl5_44 ),
    inference(avatar_split_clause,[],[f58820,f3089,f168,f9253])).

fof(f9253,plain,
    ( spl5_414
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_414])])).

fof(f168,plain,
    ( spl5_11
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f3089,plain,
    ( spl5_44
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f58820,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_11
    | spl5_44 ),
    inference(unit_resulting_resolution,[],[f4138,f442])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k3_xboole_0(sK0,sK1)))
        | r2_hidden(X0,k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) )
    | ~ spl5_11 ),
    inference(resolution,[],[f170,f45])).

fof(f170,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f4138,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_xboole_0(X0,k1_relat_1(sK1)))
    | spl5_44 ),
    inference(unit_resulting_resolution,[],[f3090,f64])).

fof(f3090,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(sK1))
    | spl5_44 ),
    inference(avatar_component_clause,[],[f3089])).

fof(f51685,plain,
    ( ~ spl5_415
    | ~ spl5_9
    | spl5_22 ),
    inference(avatar_split_clause,[],[f51517,f919,f150,f9257])).

fof(f919,plain,
    ( spl5_22
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f51517,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_9
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f4049,f379])).

fof(f4049,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_xboole_0(k2_relat_1(sK0),X0))
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f921,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f921,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(sK0))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f919])).

fof(f51316,plain,
    ( ~ spl5_414
    | ~ spl5_11
    | spl5_21 ),
    inference(avatar_split_clause,[],[f51151,f914,f168,f9253])).

fof(f914,plain,
    ( spl5_21
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f51151,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_11
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f3968,f442])).

fof(f3968,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_xboole_0(k1_relat_1(sK0),X0))
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f916,f65])).

fof(f916,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(sK0))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f914])).

fof(f9260,plain,
    ( spl5_414
    | spl5_415
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f9237,f193,f77,f9257,f9253])).

fof(f77,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f193,plain,
    ( spl5_13
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f9237,plain,
    ( r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(k3_xboole_0(sK0,sK1)))
    | r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(resolution,[],[f1303,f195])).

fof(f195,plain,
    ( r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f193])).

fof(f1303,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k3_relat_1(k3_xboole_0(sK0,X1)))
        | r2_hidden(X2,k2_relat_1(k3_xboole_0(sK0,X1)))
        | r2_hidden(X2,k1_relat_1(k3_xboole_0(sK0,X1))) )
    | ~ spl5_3 ),
    inference(superposition,[],[f62,f248])).

fof(f248,plain,
    ( ! [X0] : k3_relat_1(k3_xboole_0(sK0,X0)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k2_relat_1(k3_xboole_0(sK0,X0)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f119,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f119,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f79,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f79,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f3753,plain,
    ( ~ spl5_22
    | spl5_15
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f3751,f3611,f550,f919])).

fof(f550,plain,
    ( spl5_15
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f3611,plain,
    ( spl5_75
  <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f3751,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(sK0))
    | spl5_15
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f552,f3613,f45])).

fof(f3613,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f3611])).

fof(f552,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK0))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f550])).

fof(f3614,plain,
    ( spl5_75
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f3609,f136,f3611])).

fof(f136,plain,
    ( spl5_7
  <=> k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f3609,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f3599])).

fof(f3599,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))
    | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f734,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f734,plain,
    ( ! [X10] :
        ( r2_hidden(sK2(k2_relat_1(sK0),X10),k3_relat_1(sK0))
        | r1_tarski(k2_relat_1(sK0),X10) )
    | ~ spl5_7 ),
    inference(resolution,[],[f375,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f375,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK0))
        | r2_hidden(X2,k3_relat_1(sK0)) )
    | ~ spl5_7 ),
    inference(superposition,[],[f60,f138])).

fof(f138,plain,
    ( k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3597,plain,
    ( ~ spl5_21
    | spl5_15
    | ~ spl5_69 ),
    inference(avatar_split_clause,[],[f3595,f3536,f550,f914])).

fof(f3536,plain,
    ( spl5_69
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f3595,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(sK0))
    | spl5_15
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f552,f3538,f45])).

fof(f3538,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f3536])).

fof(f3539,plain,
    ( spl5_69
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f3534,f136,f3536])).

fof(f3534,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f3525])).

fof(f3525,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f721,f47])).

fof(f721,plain,
    ( ! [X10] :
        ( r2_hidden(sK2(k1_relat_1(sK0),X10),k3_relat_1(sK0))
        | r1_tarski(k1_relat_1(sK0),X10) )
    | ~ spl5_7 ),
    inference(resolution,[],[f374,f46])).

fof(f374,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK0))
        | r2_hidden(X1,k3_relat_1(sK0)) )
    | ~ spl5_7 ),
    inference(superposition,[],[f61,f138])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3462,plain,
    ( ~ spl5_45
    | spl5_16
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f3460,f3456,f554,f3093])).

fof(f554,plain,
    ( spl5_16
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f3456,plain,
    ( spl5_62
  <=> r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f3460,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k2_relat_1(sK1))
    | spl5_16
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f556,f3458,f45])).

fof(f3458,plain,
    ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f3456])).

fof(f556,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK1))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f554])).

fof(f3459,plain,
    ( spl5_62
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f3454,f94,f3456])).

fof(f94,plain,
    ( spl5_4
  <=> k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f3454,plain,
    ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f3446])).

fof(f3446,plain,
    ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))
    | r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f708,f47])).

fof(f708,plain,
    ( ! [X10] :
        ( r2_hidden(sK2(k2_relat_1(sK1),X10),k3_relat_1(sK1))
        | r1_tarski(k2_relat_1(sK1),X10) )
    | ~ spl5_4 ),
    inference(resolution,[],[f366,f46])).

fof(f366,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK1))
        | r2_hidden(X2,k3_relat_1(sK1)) )
    | ~ spl5_4 ),
    inference(superposition,[],[f60,f96])).

fof(f96,plain,
    ( k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f3348,plain,
    ( ~ spl5_44
    | ~ spl5_4
    | spl5_16 ),
    inference(avatar_split_clause,[],[f3306,f554,f94,f3089])).

fof(f3306,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k1_relat_1(sK1))
    | ~ spl5_4
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f556,f365])).

fof(f365,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(X1,k3_relat_1(sK1)) )
    | ~ spl5_4 ),
    inference(superposition,[],[f61,f96])).

fof(f557,plain,
    ( ~ spl5_15
    | ~ spl5_16
    | spl5_12 ),
    inference(avatar_split_clause,[],[f531,f188,f554,f550])).

fof(f188,plain,
    ( spl5_12
  <=> r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f531,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK1))
    | ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK0))
    | spl5_12 ),
    inference(resolution,[],[f190,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f190,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f188])).

fof(f196,plain,
    ( spl5_13
    | spl5_1 ),
    inference(avatar_split_clause,[],[f177,f67,f193])).

fof(f67,plain,
    ( spl5_1
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f177,plain,
    ( r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(k3_xboole_0(sK0,sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f69,f46])).

fof(f69,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f191,plain,
    ( ~ spl5_12
    | spl5_1 ),
    inference(avatar_split_clause,[],[f178,f67,f188])).

fof(f178,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f69,f47])).

fof(f176,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f134,f77,f136])).

fof(f134,plain,
    ( k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f79,f39])).

fof(f175,plain,
    ( spl5_11
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f120,f77,f72,f168])).

fof(f72,plain,
    ( spl5_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f120,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f74,f79,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f157,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f124,f77,f72,f150])).

fof(f124,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f74,f79,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f118,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f92,f72,f94])).

fof(f92,plain,
    ( k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f39])).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f75,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------

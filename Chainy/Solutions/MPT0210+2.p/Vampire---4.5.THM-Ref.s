%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0210+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:16 EST 2020

% Result     : Theorem 9.13s
% Output     : Refutation 9.13s
% Verified   : 
% Statistics : Number of formulae       :  453 (1006 expanded)
%              Number of leaves         :  102 ( 361 expanded)
%              Depth                    :   11
%              Number of atoms          : 1502 (3612 expanded)
%              Number of equality atoms :  375 ( 969 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3840,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f938,f943,f948,f974,f1005,f1033,f1037,f1041,f1046,f1050,f1139,f1144,f1166,f1237,f1273,f1278,f1297,f1334,f1336,f1413,f1423,f1427,f1429,f1533,f1535,f1621,f1651,f1653,f1694,f1747,f1842,f1880,f1903,f1909,f1913,f2042,f2116,f2212,f2320,f2365,f2372,f2422,f2457,f2830,f2834,f2863,f3043,f3064,f3078,f3080,f3086,f3090,f3162,f3163,f3324,f3377,f3383,f3434,f3458,f3479,f3493,f3495,f3566,f3707,f3775,f3780,f3784,f3789,f3811,f3837])).

fof(f3837,plain,
    ( spl23_1
    | spl23_2
    | ~ spl23_51 ),
    inference(avatar_contradiction_clause,[],[f3836])).

fof(f3836,plain,
    ( $false
    | spl23_1
    | spl23_2
    | ~ spl23_51 ),
    inference(subsumption_resolution,[],[f3835,f937])).

fof(f937,plain,
    ( sK0 != sK1
    | spl23_1 ),
    inference(avatar_component_clause,[],[f935])).

fof(f935,plain,
    ( spl23_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1])])).

fof(f3835,plain,
    ( sK0 = sK1
    | spl23_2
    | ~ spl23_51 ),
    inference(subsumption_resolution,[],[f3812,f942])).

fof(f942,plain,
    ( sK0 != sK2
    | spl23_2 ),
    inference(avatar_component_clause,[],[f940])).

fof(f940,plain,
    ( spl23_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_2])])).

fof(f3812,plain,
    ( sK0 = sK2
    | sK0 = sK1
    | ~ spl23_51 ),
    inference(resolution,[],[f3810,f877])).

fof(f877,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f700])).

fof(f700,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f448])).

fof(f448,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK14(X0,X1,X2) != X1
              & sK14(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( sK14(X0,X1,X2) = X1
            | sK14(X0,X1,X2) = X0
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f446,f447])).

fof(f447,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK14(X0,X1,X2) != X1
            & sK14(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( sK14(X0,X1,X2) = X1
          | sK14(X0,X1,X2) = X0
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f446,plain,(
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
    inference(rectify,[],[f445])).

fof(f445,plain,(
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
    inference(flattening,[],[f444])).

fof(f444,plain,(
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

fof(f3810,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | ~ spl23_51 ),
    inference(avatar_component_clause,[],[f3808])).

fof(f3808,plain,
    ( spl23_51
  <=> r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_51])])).

fof(f3811,plain,
    ( spl23_51
    | ~ spl23_40
    | ~ spl23_50 ),
    inference(avatar_split_clause,[],[f3790,f3786,f3083,f3808])).

fof(f3083,plain,
    ( spl23_40
  <=> r2_hidden(sK6(k2_tarski(sK1,sK2),k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_40])])).

fof(f3786,plain,
    ( spl23_50
  <=> r2_hidden(sK6(k2_tarski(sK1,sK2),k1_tarski(sK0)),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_50])])).

fof(f3790,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | ~ spl23_40
    | ~ spl23_50 ),
    inference(forward_demodulation,[],[f3788,f3649])).

fof(f3649,plain,
    ( sK0 = sK6(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | ~ spl23_40 ),
    inference(resolution,[],[f3085,f871])).

fof(f871,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f598])).

fof(f598,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f430])).

fof(f430,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f428,f429])).

fof(f429,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f428,plain,(
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
    inference(rectify,[],[f427])).

fof(f427,plain,(
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

fof(f3085,plain,
    ( r2_hidden(sK6(k2_tarski(sK1,sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl23_40 ),
    inference(avatar_component_clause,[],[f3083])).

fof(f3788,plain,
    ( r2_hidden(sK6(k2_tarski(sK1,sK2),k1_tarski(sK0)),k2_tarski(sK1,sK2))
    | ~ spl23_50 ),
    inference(avatar_component_clause,[],[f3786])).

fof(f3789,plain,
    ( spl23_50
    | spl23_6 ),
    inference(avatar_split_clause,[],[f1007,f998,f3786])).

fof(f998,plain,
    ( spl23_6
  <=> r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_6])])).

fof(f1007,plain,
    ( r2_hidden(sK6(k2_tarski(sK1,sK2),k1_tarski(sK0)),k2_tarski(sK1,sK2))
    | spl23_6 ),
    inference(resolution,[],[f1000,f563])).

fof(f563,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f411])).

fof(f411,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f298,f410])).

fof(f410,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f298,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1000,plain,
    ( ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl23_6 ),
    inference(avatar_component_clause,[],[f998])).

fof(f3784,plain,
    ( spl23_49
    | spl23_4 ),
    inference(avatar_split_clause,[],[f985,f967,f3782])).

fof(f3782,plain,
    ( spl23_49
  <=> ! [X3] :
        ( ~ r1_tarski(X3,k1_tarski(sK0))
        | ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_49])])).

fof(f967,plain,
    ( spl23_4
  <=> r1_tarski(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_4])])).

fof(f985,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_tarski(sK0))
        | ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),X3) )
    | spl23_4 ),
    inference(resolution,[],[f969,f683])).

fof(f683,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f362])).

fof(f362,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f361])).

fof(f361,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f969,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_4 ),
    inference(avatar_component_clause,[],[f967])).

fof(f3780,plain,
    ( ~ spl23_48
    | spl23_4 ),
    inference(avatar_split_clause,[],[f979,f967,f3777])).

fof(f3777,plain,
    ( spl23_48
  <=> r2_hidden(sK8(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_48])])).

fof(f979,plain,
    ( ~ r2_hidden(sK8(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | spl23_4 ),
    inference(resolution,[],[f969,f597])).

fof(f597,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f426])).

fof(f426,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f424,f425])).

fof(f425,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f424,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f423])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f315])).

fof(f315,plain,(
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

fof(f3775,plain,
    ( ~ spl23_47
    | ~ spl23_40 ),
    inference(avatar_split_clause,[],[f3676,f3083,f3772])).

fof(f3772,plain,
    ( spl23_47
  <=> r2_hidden(k1_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_47])])).

fof(f3676,plain,
    ( ~ r2_hidden(k1_tarski(sK0),sK0)
    | ~ spl23_40 ),
    inference(forward_demodulation,[],[f3653,f3649])).

fof(f3653,plain,
    ( ~ r2_hidden(k1_tarski(sK0),sK6(k2_tarski(sK1,sK2),k1_tarski(sK0)))
    | ~ spl23_40 ),
    inference(resolution,[],[f3085,f571])).

fof(f571,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f305])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f3707,plain,
    ( ~ spl23_36
    | ~ spl23_40 ),
    inference(avatar_split_clause,[],[f3650,f3083,f2827])).

fof(f2827,plain,
    ( spl23_36
  <=> v1_xboole_0(k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_36])])).

fof(f3650,plain,
    ( ~ v1_xboole_0(k1_tarski(sK0))
    | ~ spl23_40 ),
    inference(resolution,[],[f3085,f515])).

fof(f515,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f405])).

fof(f405,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f403,f404])).

fof(f404,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f403,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f402])).

fof(f402,plain,(
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

fof(f3566,plain,
    ( spl23_46
    | ~ spl23_39 ),
    inference(avatar_split_clause,[],[f3301,f3062,f3564])).

fof(f3564,plain,
    ( spl23_46
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_46])])).

fof(f3062,plain,
    ( spl23_39
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_39])])).

fof(f3301,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl23_39 ),
    inference(superposition,[],[f3063,f511])).

fof(f511,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f292])).

fof(f292,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f3063,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl23_39 ),
    inference(avatar_component_clause,[],[f3062])).

fof(f3495,plain,
    ( spl23_30
    | ~ spl23_33 ),
    inference(avatar_contradiction_clause,[],[f3494])).

fof(f3494,plain,
    ( $false
    | spl23_30
    | ~ spl23_33 ),
    inference(subsumption_resolution,[],[f3484,f2319])).

fof(f2319,plain,
    ( r3_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ spl23_33 ),
    inference(avatar_component_clause,[],[f2317])).

fof(f2317,plain,
    ( spl23_33
  <=> r3_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_33])])).

fof(f3484,plain,
    ( ~ r3_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | spl23_30 ),
    inference(resolution,[],[f2040,f569])).

fof(f569,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X1,X0)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f303])).

fof(f303,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X1,X0)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
     => r3_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r3_xboole_0)).

fof(f2040,plain,
    ( ~ r3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_30 ),
    inference(avatar_component_clause,[],[f2039])).

fof(f2039,plain,
    ( spl23_30
  <=> r3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_30])])).

fof(f3493,plain,
    ( spl23_4
    | spl23_30
    | ~ spl23_33 ),
    inference(avatar_contradiction_clause,[],[f3492])).

fof(f3492,plain,
    ( $false
    | spl23_4
    | spl23_30
    | ~ spl23_33 ),
    inference(subsumption_resolution,[],[f3483,f3379])).

fof(f3379,plain,
    ( r1_tarski(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | spl23_4
    | ~ spl23_33 ),
    inference(subsumption_resolution,[],[f976,f2319])).

fof(f976,plain,
    ( r1_tarski(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ r3_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | spl23_4 ),
    inference(resolution,[],[f969,f585])).

fof(f585,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f418])).

fof(f418,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f417])).

fof(f417,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f3483,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | spl23_30 ),
    inference(resolution,[],[f2040,f587])).

fof(f587,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f418])).

fof(f3479,plain,
    ( spl23_45
    | ~ spl23_39 ),
    inference(avatar_split_clause,[],[f3269,f3062,f3477])).

fof(f3477,plain,
    ( spl23_45
  <=> ! [X7] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_45])])).

fof(f3269,plain,
    ( ! [X7] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X7)
    | ~ spl23_39 ),
    inference(resolution,[],[f3063,f591])).

fof(f591,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f421])).

fof(f421,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f3458,plain,
    ( ~ spl23_14
    | spl23_4 ),
    inference(avatar_split_clause,[],[f977,f967,f1141])).

fof(f1141,plain,
    ( spl23_14
  <=> r2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_14])])).

fof(f977,plain,
    ( ~ r2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_4 ),
    inference(resolution,[],[f969,f588])).

fof(f588,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f420])).

fof(f420,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f419])).

fof(f419,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f3434,plain,
    ( spl23_44
    | ~ spl23_37 ),
    inference(avatar_split_clause,[],[f2967,f2832,f3432])).

fof(f3432,plain,
    ( spl23_44
  <=> ! [X29,X30] : ~ r2_hidden(X29,k3_xboole_0(k1_xboole_0,X30)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_44])])).

fof(f2832,plain,
    ( spl23_37
  <=> ! [X38] : ~ r2_hidden(X38,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_37])])).

fof(f2967,plain,
    ( ! [X30,X29] : ~ r2_hidden(X29,k3_xboole_0(k1_xboole_0,X30))
    | ~ spl23_37 ),
    inference(resolution,[],[f2833,f880])).

fof(f880,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f706])).

fof(f706,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f453])).

fof(f453,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
            | ~ r2_hidden(sK15(X0,X1,X2),X0)
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK15(X0,X1,X2),X1)
              & r2_hidden(sK15(X0,X1,X2),X0) )
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f451,f452])).

fof(f452,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
          | ~ r2_hidden(sK15(X0,X1,X2),X0)
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK15(X0,X1,X2),X1)
            & r2_hidden(sK15(X0,X1,X2),X0) )
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f451,plain,(
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
    inference(rectify,[],[f450])).

fof(f450,plain,(
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
    inference(flattening,[],[f449])).

fof(f449,plain,(
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

fof(f2833,plain,
    ( ! [X38] : ~ r2_hidden(X38,k1_xboole_0)
    | ~ spl23_37 ),
    inference(avatar_component_clause,[],[f2832])).

fof(f3383,plain,
    ( spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_33 ),
    inference(avatar_contradiction_clause,[],[f3382])).

fof(f3382,plain,
    ( $false
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_33 ),
    inference(subsumption_resolution,[],[f3381,f867])).

fof(f867,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f582])).

fof(f582,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f416])).

fof(f416,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f415])).

fof(f415,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3381,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_33 ),
    inference(forward_demodulation,[],[f969,f3330])).

fof(f3330,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_tarski(sK0)
    | spl23_14
    | spl23_27
    | ~ spl23_33 ),
    inference(subsumption_resolution,[],[f2326,f2319])).

fof(f2326,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_tarski(sK0)
    | ~ r3_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | spl23_14
    | spl23_27 ),
    inference(subsumption_resolution,[],[f2081,f1902])).

fof(f1902,plain,
    ( ~ r2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | spl23_27 ),
    inference(avatar_component_clause,[],[f1900])).

fof(f1900,plain,
    ( spl23_27
  <=> r2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_27])])).

fof(f2081,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_tarski(sK0)
    | r2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ r3_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | spl23_14 ),
    inference(resolution,[],[f1143,f609])).

fof(f609,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X1,X0)
      | X0 = X1
      | r2_xboole_0(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f434])).

fof(f434,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1)
        | ~ r3_xboole_0(X0,X1) )
      & ( r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(flattening,[],[f433])).

fof(f433,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1)
        | ~ r3_xboole_0(X0,X1) )
      & ( r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(nnf_transformation,[],[f316])).

fof(f316,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] :
      ( ~ ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_xboole_1)).

fof(f1143,plain,
    ( ~ r2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_14 ),
    inference(avatar_component_clause,[],[f1141])).

fof(f3377,plain,
    ( spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_33 ),
    inference(avatar_contradiction_clause,[],[f3376])).

fof(f3376,plain,
    ( $false
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_33 ),
    inference(subsumption_resolution,[],[f3375,f3374])).

fof(f3374,plain,
    ( ~ r2_hidden(sK8(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0))
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_33 ),
    inference(forward_demodulation,[],[f979,f3330])).

fof(f3375,plain,
    ( r2_hidden(sK8(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0))
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_33 ),
    inference(forward_demodulation,[],[f978,f3330])).

fof(f978,plain,
    ( r2_hidden(sK8(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)),k1_enumset1(sK0,sK1,sK2))
    | spl23_4 ),
    inference(resolution,[],[f969,f596])).

fof(f596,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f426])).

fof(f3324,plain,
    ( spl23_43
    | ~ spl23_4 ),
    inference(avatar_split_clause,[],[f1472,f967,f3322])).

fof(f3322,plain,
    ( spl23_43
  <=> ! [X3] : r1_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(X3,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_43])])).

fof(f1472,plain,
    ( ! [X3] : r1_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(X3,k1_tarski(sK0)))
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f659])).

fof(f659,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f331])).

fof(f331,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f155])).

fof(f155,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f968,plain,
    ( r1_tarski(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | ~ spl23_4 ),
    inference(avatar_component_clause,[],[f967])).

fof(f3163,plain,
    ( spl23_21
    | ~ spl23_4 ),
    inference(avatar_split_clause,[],[f1468,f967,f1420])).

fof(f1420,plain,
    ( spl23_21
  <=> k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_21])])).

fof(f1468,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f605])).

fof(f605,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f432])).

fof(f432,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f3162,plain,
    ( ~ spl23_42
    | spl23_6 ),
    inference(avatar_split_clause,[],[f1026,f998,f3159])).

fof(f3159,plain,
    ( spl23_42
  <=> r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_42])])).

fof(f1026,plain,
    ( ~ r1_xboole_0(k3_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | spl23_6 ),
    inference(forward_demodulation,[],[f1012,f529])).

fof(f529,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1012,plain,
    ( ~ r1_xboole_0(k3_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | spl23_6 ),
    inference(resolution,[],[f1000,f611])).

fof(f611,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f318])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f143])).

fof(f143,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f3090,plain,
    ( spl23_41
    | spl23_6 ),
    inference(avatar_split_clause,[],[f1016,f998,f3088])).

fof(f3088,plain,
    ( spl23_41
  <=> ! [X3] :
        ( ~ r1_xboole_0(X3,k1_tarski(sK0))
        | ~ r1_tarski(k2_tarski(sK1,sK2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_41])])).

fof(f1016,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(X3,k1_tarski(sK0))
        | ~ r1_tarski(k2_tarski(sK1,sK2),X3) )
    | spl23_6 ),
    inference(resolution,[],[f1000,f680])).

fof(f680,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f356])).

fof(f356,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f355])).

fof(f355,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f129])).

fof(f129,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f3086,plain,
    ( spl23_40
    | spl23_6 ),
    inference(avatar_split_clause,[],[f1008,f998,f3083])).

fof(f1008,plain,
    ( r2_hidden(sK6(k2_tarski(sK1,sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | spl23_6 ),
    inference(resolution,[],[f1000,f564])).

fof(f564,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f411])).

fof(f3080,plain,(
    spl23_32 ),
    inference(avatar_contradiction_clause,[],[f3079])).

fof(f3079,plain,
    ( $false
    | spl23_32 ),
    inference(subsumption_resolution,[],[f3073,f867])).

fof(f3073,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_32 ),
    inference(trivial_inequality_removal,[],[f3071])).

fof(f3071,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_32 ),
    inference(superposition,[],[f2210,f603])).

fof(f603,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f431])).

fof(f431,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2210,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_32 ),
    inference(avatar_component_clause,[],[f2209])).

fof(f2209,plain,
    ( spl23_32
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_32])])).

fof(f3078,plain,(
    spl23_32 ),
    inference(avatar_contradiction_clause,[],[f3077])).

fof(f3077,plain,
    ( $false
    | spl23_32 ),
    inference(subsumption_resolution,[],[f3074,f867])).

fof(f3074,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_32 ),
    inference(trivial_inequality_removal,[],[f3070])).

fof(f3070,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_32 ),
    inference(superposition,[],[f2210,f605])).

fof(f3064,plain,
    ( spl23_39
    | ~ spl23_37 ),
    inference(avatar_split_clause,[],[f2950,f2832,f3062])).

fof(f2950,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl23_37 ),
    inference(resolution,[],[f2833,f563])).

fof(f3043,plain,
    ( ~ spl23_27
    | ~ spl23_4 ),
    inference(avatar_split_clause,[],[f1469,f967,f1900])).

fof(f1469,plain,
    ( ~ r2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f617])).

fof(f617,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f323])).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f126])).

fof(f126,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f2863,plain,
    ( spl23_38
    | ~ spl23_4
    | spl23_14
    | ~ spl23_32
    | spl23_35 ),
    inference(avatar_split_clause,[],[f2855,f2823,f2209,f1141,f967,f2861])).

fof(f2861,plain,
    ( spl23_38
  <=> ! [X18] :
        ( ~ r1_tarski(k1_tarski(sK0),X18)
        | ~ r1_xboole_0(k1_tarski(sK0),X18) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_38])])).

fof(f2823,plain,
    ( spl23_35
  <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_35])])).

fof(f2855,plain,
    ( ! [X18] :
        ( ~ r1_tarski(k1_tarski(sK0),X18)
        | ~ r1_xboole_0(k1_tarski(sK0),X18) )
    | ~ spl23_4
    | spl23_14
    | ~ spl23_32
    | spl23_35 ),
    inference(subsumption_resolution,[],[f1558,f2852])).

fof(f2852,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | ~ spl23_32
    | spl23_35 ),
    inference(forward_demodulation,[],[f2840,f2211])).

fof(f2211,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl23_32 ),
    inference(avatar_component_clause,[],[f2209])).

fof(f2840,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_35 ),
    inference(resolution,[],[f2825,f594])).

fof(f594,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f422])).

fof(f422,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f2825,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_35 ),
    inference(avatar_component_clause,[],[f2823])).

fof(f1558,plain,
    ( ! [X18] :
        ( ~ r1_tarski(k1_tarski(sK0),X18)
        | k1_xboole_0 = k1_tarski(sK0)
        | ~ r1_xboole_0(k1_tarski(sK0),X18) )
    | ~ spl23_4
    | spl23_14 ),
    inference(forward_demodulation,[],[f1557,f1428])).

fof(f1428,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_tarski(sK0)
    | ~ spl23_4
    | spl23_14 ),
    inference(subsumption_resolution,[],[f1217,f968])).

fof(f1217,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_tarski(sK0)
    | ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_14 ),
    inference(resolution,[],[f1143,f590])).

fof(f590,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f420])).

fof(f1557,plain,
    ( ! [X18] :
        ( k1_xboole_0 = k1_tarski(sK0)
        | ~ r1_xboole_0(k1_tarski(sK0),X18)
        | ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),X18) )
    | ~ spl23_4
    | spl23_14 ),
    inference(forward_demodulation,[],[f1487,f1428])).

fof(f1487,plain,
    ( ! [X18] :
        ( k1_xboole_0 = k1_enumset1(sK0,sK1,sK2)
        | ~ r1_xboole_0(k1_tarski(sK0),X18)
        | ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),X18) )
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f682])).

fof(f682,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f360])).

fof(f360,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f359])).

fof(f359,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f133])).

fof(f133,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f2834,plain,
    ( spl23_37
    | ~ spl23_32 ),
    inference(avatar_split_clause,[],[f2821,f2209,f2832])).

fof(f2821,plain,
    ( ! [X38] : ~ r2_hidden(X38,k1_xboole_0)
    | ~ spl23_32 ),
    inference(subsumption_resolution,[],[f2790,f2789])).

fof(f2789,plain,
    ( ! [X37] :
        ( ~ r2_hidden(X37,k1_xboole_0)
        | ~ r2_hidden(X37,k1_tarski(sK0)) )
    | ~ spl23_32 ),
    inference(superposition,[],[f882,f2211])).

fof(f882,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f713])).

fof(f713,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f458])).

fof(f458,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK16(X0,X1,X2),X1)
            | ~ r2_hidden(sK16(X0,X1,X2),X0)
            | ~ r2_hidden(sK16(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK16(X0,X1,X2),X1)
              & r2_hidden(sK16(X0,X1,X2),X0) )
            | r2_hidden(sK16(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f456,f457])).

fof(f457,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK16(X0,X1,X2),X1)
          | ~ r2_hidden(sK16(X0,X1,X2),X0)
          | ~ r2_hidden(sK16(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK16(X0,X1,X2),X1)
            & r2_hidden(sK16(X0,X1,X2),X0) )
          | r2_hidden(sK16(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f456,plain,(
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
    inference(rectify,[],[f455])).

fof(f455,plain,(
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
    inference(flattening,[],[f454])).

fof(f454,plain,(
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

fof(f2790,plain,
    ( ! [X38] :
        ( ~ r2_hidden(X38,k1_xboole_0)
        | r2_hidden(X38,k1_tarski(sK0)) )
    | ~ spl23_32 ),
    inference(superposition,[],[f883,f2211])).

fof(f883,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f712])).

fof(f712,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f458])).

fof(f2830,plain,
    ( ~ spl23_35
    | spl23_36
    | ~ spl23_4
    | spl23_14 ),
    inference(avatar_split_clause,[],[f1525,f1141,f967,f2827,f2823])).

fof(f1525,plain,
    ( v1_xboole_0(k1_tarski(sK0))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl23_4
    | spl23_14 ),
    inference(forward_demodulation,[],[f1524,f1428])).

fof(f1524,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | v1_xboole_0(k1_enumset1(sK0,sK1,sK2))
    | ~ spl23_4
    | spl23_14 ),
    inference(forward_demodulation,[],[f1457,f1428])).

fof(f1457,plain,
    ( ~ r1_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | v1_xboole_0(k1_enumset1(sK0,sK1,sK2))
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f568])).

fof(f568,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f302])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f301])).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f135,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f2457,plain,
    ( spl23_34
    | spl23_4
    | ~ spl23_30 ),
    inference(avatar_split_clause,[],[f2368,f2039,f967,f2454])).

fof(f2454,plain,
    ( spl23_34
  <=> r1_tarski(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_34])])).

fof(f2368,plain,
    ( r1_tarski(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | spl23_4
    | ~ spl23_30 ),
    inference(subsumption_resolution,[],[f975,f2041])).

fof(f2041,plain,
    ( r3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | ~ spl23_30 ),
    inference(avatar_component_clause,[],[f2039])).

fof(f975,plain,
    ( r1_tarski(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ r3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_4 ),
    inference(resolution,[],[f969,f585])).

fof(f2422,plain,
    ( ~ spl23_14
    | spl23_4 ),
    inference(avatar_split_clause,[],[f977,f967,f1141])).

fof(f2372,plain,
    ( spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_30 ),
    inference(avatar_contradiction_clause,[],[f2371])).

fof(f2371,plain,
    ( $false
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_30 ),
    inference(subsumption_resolution,[],[f2370,f867])).

fof(f2370,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_30 ),
    inference(forward_demodulation,[],[f969,f2328])).

fof(f2328,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_tarski(sK0)
    | spl23_14
    | spl23_27
    | ~ spl23_30 ),
    inference(subsumption_resolution,[],[f2327,f2041])).

fof(f2327,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k1_tarski(sK0)
    | ~ r3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_14
    | spl23_27 ),
    inference(subsumption_resolution,[],[f2080,f1902])).

fof(f2080,plain,
    ( r2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k1_tarski(sK0)
    | ~ r3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_14 ),
    inference(resolution,[],[f1143,f609])).

fof(f2365,plain,
    ( spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_30 ),
    inference(avatar_contradiction_clause,[],[f2364])).

fof(f2364,plain,
    ( $false
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_30 ),
    inference(subsumption_resolution,[],[f2363,f2362])).

fof(f2362,plain,
    ( ~ r2_hidden(sK8(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0))
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_30 ),
    inference(forward_demodulation,[],[f979,f2328])).

fof(f2363,plain,
    ( r2_hidden(sK8(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0))
    | spl23_4
    | spl23_14
    | spl23_27
    | ~ spl23_30 ),
    inference(forward_demodulation,[],[f978,f2328])).

fof(f2320,plain,
    ( spl23_33
    | ~ spl23_4 ),
    inference(avatar_split_clause,[],[f1464,f967,f2317])).

fof(f1464,plain,
    ( r3_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f587])).

fof(f2212,plain,
    ( spl23_32
    | ~ spl23_4
    | spl23_14 ),
    inference(avatar_split_clause,[],[f1616,f1141,f967,f2209])).

fof(f1616,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl23_4
    | spl23_14 ),
    inference(forward_demodulation,[],[f1468,f1428])).

fof(f2116,plain,
    ( spl23_31
    | spl23_4 ),
    inference(avatar_split_clause,[],[f984,f967,f2114])).

fof(f2114,plain,
    ( spl23_31
  <=> ! [X2] : ~ r1_tarski(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),X2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_31])])).

fof(f984,plain,
    ( ! [X2] : ~ r1_tarski(k2_xboole_0(k1_enumset1(sK0,sK1,sK2),X2),k1_tarski(sK0))
    | spl23_4 ),
    inference(resolution,[],[f969,f675])).

fof(f675,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f346])).

fof(f346,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f2042,plain,
    ( spl23_30
    | ~ spl23_4 ),
    inference(avatar_split_clause,[],[f1463,f967,f2039])).

fof(f1463,plain,
    ( r3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f586])).

fof(f586,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f418])).

fof(f1913,plain,
    ( spl23_29
    | ~ spl23_4
    | spl23_14 ),
    inference(avatar_split_clause,[],[f1542,f1141,f967,f1911])).

fof(f1911,plain,
    ( spl23_29
  <=> ! [X4] : r1_tarski(k1_tarski(sK0),k2_xboole_0(X4,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_29])])).

fof(f1542,plain,
    ( ! [X4] : r1_tarski(k1_tarski(sK0),k2_xboole_0(X4,k1_tarski(sK0)))
    | ~ spl23_4
    | spl23_14 ),
    inference(forward_demodulation,[],[f1473,f1428])).

fof(f1473,plain,
    ( ! [X4] : r1_tarski(k1_enumset1(sK0,sK1,sK2),k2_xboole_0(X4,k1_tarski(sK0)))
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f660])).

fof(f660,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f332])).

fof(f332,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1909,plain,
    ( ~ spl23_28
    | ~ spl23_24 ),
    inference(avatar_split_clause,[],[f1871,f1649,f1906])).

fof(f1906,plain,
    ( spl23_28
  <=> r1_tarski(k2_tarski(sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_28])])).

fof(f1649,plain,
    ( spl23_24
  <=> ! [X2] : ~ r1_tarski(k2_tarski(sK1,sK2),k4_xboole_0(X2,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_24])])).

fof(f1871,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK2),k1_xboole_0)
    | ~ spl23_24 ),
    inference(superposition,[],[f1650,f497])).

fof(f497,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f1650,plain,
    ( ! [X2] : ~ r1_tarski(k2_tarski(sK1,sK2),k4_xboole_0(X2,k1_tarski(sK0)))
    | ~ spl23_24 ),
    inference(avatar_component_clause,[],[f1649])).

fof(f1903,plain,
    ( ~ spl23_27
    | ~ spl23_4 ),
    inference(avatar_split_clause,[],[f1469,f967,f1900])).

fof(f1880,plain,
    ( spl23_26
    | spl23_4 ),
    inference(avatar_split_clause,[],[f983,f967,f1878])).

fof(f1878,plain,
    ( spl23_26
  <=> ! [X1] : ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_26])])).

fof(f983,plain,
    ( ! [X1] : ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k1_tarski(sK0),X1))
    | spl23_4 ),
    inference(resolution,[],[f969,f671])).

fof(f671,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f343])).

fof(f343,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1842,plain,
    ( spl23_25
    | ~ spl23_20 ),
    inference(avatar_split_clause,[],[f1387,f1332,f1840])).

fof(f1840,plain,
    ( spl23_25
  <=> ! [X5] : ~ r1_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_25])])).

fof(f1332,plain,
    ( spl23_20
  <=> ! [X0] : ~ r1_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_20])])).

fof(f1387,plain,
    ( ! [X5] : ~ r1_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,X5))
    | ~ spl23_20 ),
    inference(superposition,[],[f1333,f540])).

fof(f540,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f1333,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK0),X0))
    | ~ spl23_20 ),
    inference(avatar_component_clause,[],[f1332])).

fof(f1747,plain,
    ( ~ spl23_6
    | ~ spl23_20 ),
    inference(avatar_split_clause,[],[f1408,f1332,f998])).

fof(f1408,plain,
    ( ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | ~ spl23_20 ),
    inference(condensation,[],[f1365])).

fof(f1365,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_tarski(sK1,sK2),X0)
        | ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)) )
    | ~ spl23_20 ),
    inference(resolution,[],[f1333,f651])).

fof(f651,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f324])).

fof(f324,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f138])).

fof(f138,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1694,plain,
    ( spl23_3
    | ~ spl23_6 ),
    inference(avatar_contradiction_clause,[],[f1693])).

fof(f1693,plain,
    ( $false
    | spl23_3
    | ~ spl23_6 ),
    inference(subsumption_resolution,[],[f1692,f947])).

fof(f947,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
    | spl23_3 ),
    inference(avatar_component_clause,[],[f945])).

fof(f945,plain,
    ( spl23_3
  <=> k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_3])])).

fof(f1692,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) = k2_tarski(sK1,sK2)
    | ~ spl23_6 ),
    inference(forward_demodulation,[],[f1691,f619])).

fof(f619,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f283])).

fof(f283,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f1691,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_tarski(sK0))
    | ~ spl23_6 ),
    inference(forward_demodulation,[],[f1690,f620])).

fof(f620,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f282])).

fof(f282,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f1690,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k1_enumset1(sK1,sK2,sK0),k1_tarski(sK0))
    | ~ spl23_6 ),
    inference(forward_demodulation,[],[f1658,f625])).

fof(f625,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f228])).

fof(f228,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f1658,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl23_6 ),
    inference(resolution,[],[f999,f573])).

fof(f573,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f307])).

fof(f307,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f158])).

fof(f158,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f999,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | ~ spl23_6 ),
    inference(avatar_component_clause,[],[f998])).

fof(f1653,plain,
    ( ~ spl23_6
    | spl23_18 ),
    inference(avatar_contradiction_clause,[],[f1652])).

fof(f1652,plain,
    ( $false
    | ~ spl23_6
    | spl23_18 ),
    inference(subsumption_resolution,[],[f999,f1359])).

fof(f1359,plain,
    ( ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl23_18 ),
    inference(trivial_inequality_removal,[],[f1352])).

fof(f1352,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl23_18 ),
    inference(superposition,[],[f1277,f591])).

fof(f1277,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl23_18 ),
    inference(avatar_component_clause,[],[f1275])).

fof(f1275,plain,
    ( spl23_18
  <=> k1_xboole_0 = k3_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_18])])).

fof(f1651,plain,
    ( spl23_24
    | spl23_6 ),
    inference(avatar_split_clause,[],[f1015,f998,f1649])).

fof(f1015,plain,
    ( ! [X2] : ~ r1_tarski(k2_tarski(sK1,sK2),k4_xboole_0(X2,k1_tarski(sK0)))
    | spl23_6 ),
    inference(resolution,[],[f1000,f672])).

fof(f672,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f343])).

fof(f1621,plain,
    ( spl23_23
    | ~ spl23_4
    | spl23_14 ),
    inference(avatar_split_clause,[],[f1541,f1141,f967,f1619])).

fof(f1619,plain,
    ( spl23_23
  <=> ! [X3] : r1_xboole_0(k1_tarski(sK0),k4_xboole_0(X3,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_23])])).

fof(f1541,plain,
    ( ! [X3] : r1_xboole_0(k1_tarski(sK0),k4_xboole_0(X3,k1_tarski(sK0)))
    | ~ spl23_4
    | spl23_14 ),
    inference(forward_demodulation,[],[f1472,f1428])).

fof(f1535,plain,
    ( ~ spl23_4
    | spl23_21 ),
    inference(avatar_contradiction_clause,[],[f1534])).

fof(f1534,plain,
    ( $false
    | ~ spl23_4
    | spl23_21 ),
    inference(subsumption_resolution,[],[f1468,f1422])).

fof(f1422,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_21 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f1533,plain,
    ( ~ spl23_4
    | spl23_21 ),
    inference(avatar_contradiction_clause,[],[f1532])).

fof(f1532,plain,
    ( $false
    | ~ spl23_4
    | spl23_21 ),
    inference(subsumption_resolution,[],[f1467,f1422])).

fof(f1467,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | ~ spl23_4 ),
    inference(resolution,[],[f968,f603])).

fof(f1429,plain,
    ( ~ spl23_6
    | spl23_11 ),
    inference(avatar_split_clause,[],[f1084,f1043,f998])).

fof(f1043,plain,
    ( spl23_11
  <=> r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_11])])).

fof(f1084,plain,
    ( ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl23_11 ),
    inference(resolution,[],[f1045,f572])).

fof(f572,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f306])).

fof(f306,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1045,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | spl23_11 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1427,plain,
    ( spl23_22
    | spl23_4 ),
    inference(avatar_split_clause,[],[f982,f967,f1425])).

fof(f1425,plain,
    ( spl23_22
  <=> ! [X0] : ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_tarski(sK0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_22])])).

fof(f982,plain,
    ( ! [X0] : ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_tarski(sK0),X0))
    | spl23_4 ),
    inference(resolution,[],[f969,f670])).

fof(f670,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f342])).

fof(f342,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f1423,plain,
    ( ~ spl23_21
    | spl23_4 ),
    inference(avatar_split_clause,[],[f980,f967,f1420])).

fof(f980,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_4 ),
    inference(resolution,[],[f969,f602])).

fof(f602,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f431])).

fof(f1413,plain,
    ( ~ spl23_5
    | spl23_18 ),
    inference(avatar_split_clause,[],[f1364,f1275,f971])).

fof(f971,plain,
    ( spl23_5
  <=> k1_xboole_0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_5])])).

fof(f1364,plain,
    ( k1_xboole_0 != k2_tarski(sK1,sK2)
    | spl23_18 ),
    inference(subsumption_resolution,[],[f1363,f495])).

fof(f495,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1363,plain,
    ( k1_xboole_0 != k2_tarski(sK1,sK2)
    | ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | spl23_18 ),
    inference(inner_rewriting,[],[f1351])).

fof(f1351,plain,
    ( k1_xboole_0 != k2_tarski(sK1,sK2)
    | ~ r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl23_18 ),
    inference(superposition,[],[f1277,f574])).

fof(f574,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f308])).

fof(f308,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1336,plain,
    ( ~ spl23_6
    | spl23_11 ),
    inference(avatar_contradiction_clause,[],[f1335])).

fof(f1335,plain,
    ( $false
    | ~ spl23_6
    | spl23_11 ),
    inference(subsumption_resolution,[],[f999,f1084])).

fof(f1334,plain,
    ( spl23_20
    | spl23_6 ),
    inference(avatar_split_clause,[],[f1013,f998,f1332])).

fof(f1013,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK0),X0))
    | spl23_6 ),
    inference(resolution,[],[f1000,f652])).

fof(f652,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f324])).

fof(f1297,plain,
    ( spl23_19
    | spl23_3 ),
    inference(avatar_split_clause,[],[f957,f945,f1295])).

fof(f1295,plain,
    ( spl23_19
  <=> ! [X2] :
        ( k2_tarski(sK1,sK2) != X2
        | r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),k1_tarski(sK0))
        | ~ r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),k1_enumset1(sK0,sK1,sK2))
        | ~ r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_19])])).

fof(f957,plain,
    ( ! [X2] :
        ( k2_tarski(sK1,sK2) != X2
        | r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),k1_tarski(sK0))
        | ~ r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),k1_enumset1(sK0,sK1,sK2))
        | ~ r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X2),X2) )
    | spl23_3 ),
    inference(superposition,[],[f947,f717])).

fof(f717,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK16(X0,X1,X2),X1)
      | ~ r2_hidden(sK16(X0,X1,X2),X0)
      | ~ r2_hidden(sK16(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f458])).

fof(f1278,plain,
    ( ~ spl23_18
    | spl23_6 ),
    inference(avatar_split_clause,[],[f1010,f998,f1275])).

fof(f1010,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl23_6 ),
    inference(resolution,[],[f1000,f592])).

fof(f592,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f421])).

fof(f1273,plain,
    ( spl23_17
    | spl23_3 ),
    inference(avatar_split_clause,[],[f949,f945,f1271])).

fof(f1271,plain,
    ( spl23_17
  <=> ! [X0] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X0,k1_tarski(sK0))
        | sK2 = sK18(sK0,sK1,sK2,X0)
        | sK1 = sK18(sK0,sK1,sK2,X0)
        | sK0 = sK18(sK0,sK1,sK2,X0)
        | r2_hidden(sK18(sK0,sK1,sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_17])])).

fof(f949,plain,
    ( ! [X0] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X0,k1_tarski(sK0))
        | sK2 = sK18(sK0,sK1,sK2,X0)
        | sK1 = sK18(sK0,sK1,sK2,X0)
        | sK0 = sK18(sK0,sK1,sK2,X0)
        | r2_hidden(sK18(sK0,sK1,sK2,X0),X0) )
    | spl23_3 ),
    inference(superposition,[],[f947,f775])).

fof(f775,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK18(X0,X1,X2,X3) = X2
      | sK18(X0,X1,X2,X3) = X1
      | sK18(X0,X1,X2,X3) = X0
      | r2_hidden(sK18(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f471])).

fof(f471,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK18(X0,X1,X2,X3) != X2
              & sK18(X0,X1,X2,X3) != X1
              & sK18(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK18(X0,X1,X2,X3),X3) )
          & ( sK18(X0,X1,X2,X3) = X2
            | sK18(X0,X1,X2,X3) = X1
            | sK18(X0,X1,X2,X3) = X0
            | r2_hidden(sK18(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f469,f470])).

fof(f470,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK18(X0,X1,X2,X3) != X2
            & sK18(X0,X1,X2,X3) != X1
            & sK18(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK18(X0,X1,X2,X3),X3) )
        & ( sK18(X0,X1,X2,X3) = X2
          | sK18(X0,X1,X2,X3) = X1
          | sK18(X0,X1,X2,X3) = X0
          | r2_hidden(sK18(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f469,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f468])).

fof(f468,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f467])).

fof(f467,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f397])).

fof(f397,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f174])).

fof(f174,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1237,plain,
    ( spl23_16
    | spl23_3 ),
    inference(avatar_split_clause,[],[f955,f945,f1235])).

fof(f1235,plain,
    ( spl23_16
  <=> ! [X0] :
        ( k2_tarski(sK1,sK2) != X0
        | r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X0),k1_enumset1(sK0,sK1,sK2))
        | r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_16])])).

fof(f955,plain,
    ( ! [X0] :
        ( k2_tarski(sK1,sK2) != X0
        | r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X0),k1_enumset1(sK0,sK1,sK2))
        | r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X0),X0) )
    | spl23_3 ),
    inference(superposition,[],[f947,f715])).

fof(f715,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK16(X0,X1,X2),X0)
      | r2_hidden(sK16(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f458])).

fof(f1166,plain,
    ( spl23_15
    | spl23_3 ),
    inference(avatar_split_clause,[],[f956,f945,f1164])).

fof(f1164,plain,
    ( spl23_15
  <=> ! [X1] :
        ( k2_tarski(sK1,sK2) != X1
        | ~ r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X1),k1_tarski(sK0))
        | r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_15])])).

fof(f956,plain,
    ( ! [X1] :
        ( k2_tarski(sK1,sK2) != X1
        | ~ r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X1),k1_tarski(sK0))
        | r2_hidden(sK16(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0),X1),X1) )
    | spl23_3 ),
    inference(superposition,[],[f947,f716])).

fof(f716,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK16(X0,X1,X2),X1)
      | r2_hidden(sK16(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f458])).

fof(f1144,plain,
    ( ~ spl23_14
    | spl23_4 ),
    inference(avatar_split_clause,[],[f977,f967,f1141])).

fof(f1139,plain,
    ( spl23_13
    | spl23_3 ),
    inference(avatar_split_clause,[],[f953,f945,f1137])).

fof(f1137,plain,
    ( spl23_13
  <=> ! [X0] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(k1_enumset1(sK0,sK1,sK2),X0)
        | sK0 = sK9(sK0,X0)
        | r2_hidden(sK9(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_13])])).

fof(f953,plain,
    ( ! [X0] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(k1_enumset1(sK0,sK1,sK2),X0)
        | sK0 = sK9(sK0,X0)
        | r2_hidden(sK9(sK0,X0),X0) )
    | spl23_3 ),
    inference(superposition,[],[f947,f600])).

fof(f600,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK9(X0,X1) = X0
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f430])).

fof(f1050,plain,
    ( spl23_12
    | spl23_3 ),
    inference(avatar_split_clause,[],[f964,f945,f1048])).

fof(f1048,plain,
    ( spl23_12
  <=> ! [X1] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(k1_enumset1(sK0,sK1,sK2),X1)
        | sK0 != sK9(sK0,X1)
        | ~ r2_hidden(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_12])])).

fof(f964,plain,
    ( ! [X1] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(k1_enumset1(sK0,sK1,sK2),X1)
        | sK0 != sK9(sK0,X1)
        | ~ r2_hidden(sK0,X1) )
    | spl23_3 ),
    inference(inner_rewriting,[],[f954])).

fof(f954,plain,
    ( ! [X1] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(k1_enumset1(sK0,sK1,sK2),X1)
        | sK0 != sK9(sK0,X1)
        | ~ r2_hidden(sK9(sK0,X1),X1) )
    | spl23_3 ),
    inference(superposition,[],[f947,f601])).

fof(f601,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK9(X0,X1) != X0
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f430])).

fof(f1046,plain,
    ( ~ spl23_11
    | spl23_6 ),
    inference(avatar_split_clause,[],[f1009,f998,f1043])).

fof(f1009,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | spl23_6 ),
    inference(resolution,[],[f1000,f572])).

fof(f1041,plain,
    ( spl23_10
    | spl23_3 ),
    inference(avatar_split_clause,[],[f963,f945,f1039])).

fof(f1039,plain,
    ( spl23_10
  <=> ! [X3] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X3,k1_tarski(sK0))
        | sK2 != sK18(sK0,sK1,sK2,X3)
        | ~ r2_hidden(sK2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_10])])).

fof(f963,plain,
    ( ! [X3] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X3,k1_tarski(sK0))
        | sK2 != sK18(sK0,sK1,sK2,X3)
        | ~ r2_hidden(sK2,X3) )
    | spl23_3 ),
    inference(inner_rewriting,[],[f952])).

fof(f952,plain,
    ( ! [X3] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X3,k1_tarski(sK0))
        | sK2 != sK18(sK0,sK1,sK2,X3)
        | ~ r2_hidden(sK18(sK0,sK1,sK2,X3),X3) )
    | spl23_3 ),
    inference(superposition,[],[f947,f778])).

fof(f778,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK18(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK18(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f471])).

fof(f1037,plain,
    ( spl23_9
    | spl23_3 ),
    inference(avatar_split_clause,[],[f962,f945,f1035])).

fof(f1035,plain,
    ( spl23_9
  <=> ! [X2] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X2,k1_tarski(sK0))
        | sK1 != sK18(sK0,sK1,sK2,X2)
        | ~ r2_hidden(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_9])])).

fof(f962,plain,
    ( ! [X2] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X2,k1_tarski(sK0))
        | sK1 != sK18(sK0,sK1,sK2,X2)
        | ~ r2_hidden(sK1,X2) )
    | spl23_3 ),
    inference(inner_rewriting,[],[f951])).

fof(f951,plain,
    ( ! [X2] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X2,k1_tarski(sK0))
        | sK1 != sK18(sK0,sK1,sK2,X2)
        | ~ r2_hidden(sK18(sK0,sK1,sK2,X2),X2) )
    | spl23_3 ),
    inference(superposition,[],[f947,f777])).

fof(f777,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK18(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK18(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f471])).

fof(f1033,plain,
    ( spl23_8
    | spl23_3 ),
    inference(avatar_split_clause,[],[f961,f945,f1031])).

fof(f1031,plain,
    ( spl23_8
  <=> ! [X1] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X1,k1_tarski(sK0))
        | sK0 != sK18(sK0,sK1,sK2,X1)
        | ~ r2_hidden(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_8])])).

fof(f961,plain,
    ( ! [X1] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X1,k1_tarski(sK0))
        | sK0 != sK18(sK0,sK1,sK2,X1)
        | ~ r2_hidden(sK0,X1) )
    | spl23_3 ),
    inference(inner_rewriting,[],[f950])).

fof(f950,plain,
    ( ! [X1] :
        ( k2_tarski(sK1,sK2) != k4_xboole_0(X1,k1_tarski(sK0))
        | sK0 != sK18(sK0,sK1,sK2,X1)
        | ~ r2_hidden(sK18(sK0,sK1,sK2,X1),X1) )
    | spl23_3 ),
    inference(superposition,[],[f947,f776])).

fof(f776,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK18(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK18(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f471])).

fof(f1005,plain,
    ( ~ spl23_6
    | ~ spl23_7
    | spl23_3 ),
    inference(avatar_split_clause,[],[f965,f945,f1002,f998])).

fof(f1002,plain,
    ( spl23_7
  <=> k1_enumset1(sK0,sK1,sK2) = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_7])])).

fof(f965,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_tarski(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))
    | spl23_3 ),
    inference(inner_rewriting,[],[f960])).

fof(f960,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_tarski(sK1,sK2)
    | ~ r1_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_3 ),
    inference(superposition,[],[f947,f593])).

fof(f593,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f422])).

fof(f974,plain,
    ( ~ spl23_4
    | ~ spl23_5
    | spl23_3 ),
    inference(avatar_split_clause,[],[f958,f945,f971,f967])).

fof(f958,plain,
    ( k1_xboole_0 != k2_tarski(sK1,sK2)
    | ~ r1_tarski(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0))
    | spl23_3 ),
    inference(superposition,[],[f947,f605])).

fof(f948,plain,(
    ~ spl23_3 ),
    inference(avatar_split_clause,[],[f488,f945])).

fof(f488,plain,(
    k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f401])).

fof(f401,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
    & sK0 != sK2
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f290,f400])).

fof(f400,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 )
   => ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK0)) != k2_tarski(sK1,sK2)
      & sK0 != sK2
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f290,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
      & X0 != X2
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f225])).

fof(f225,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
          & X0 != X2
          & X0 != X1 ) ),
    inference(negated_conjecture,[],[f224])).

fof(f224,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).

fof(f943,plain,(
    ~ spl23_2 ),
    inference(avatar_split_clause,[],[f487,f940])).

fof(f487,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f401])).

fof(f938,plain,(
    ~ spl23_1 ),
    inference(avatar_split_clause,[],[f486,f935])).

fof(f486,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f401])).
%------------------------------------------------------------------------------

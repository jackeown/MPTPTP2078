%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:03 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 238 expanded)
%              Number of leaves         :   23 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  215 ( 424 expanded)
%              Number of equality atoms :   67 ( 166 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1945,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f299,f301,f487,f535,f1517,f1682,f1746,f1913,f1922,f1944])).

fof(f1944,plain,
    ( spl5_45
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f1943,f1919,f1149])).

fof(f1149,plain,
    ( spl5_45
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1919,plain,
    ( spl5_75
  <=> r1_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f1943,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f1942,f186])).

fof(f186,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f178,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f178,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f142,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f142,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f136,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f136,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f45,f25])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1942,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f1931,f42])).

fof(f1931,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ spl5_75 ),
    inference(resolution,[],[f1921,f45])).

fof(f1921,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f1919])).

fof(f1922,plain,
    ( spl5_75
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f1914,f1910,f1919])).

fof(f1910,plain,
    ( spl5_74
  <=> r1_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f1914,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_74 ),
    inference(resolution,[],[f1912,f417])).

fof(f417,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f414])).

fof(f414,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f107,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(X3,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f35,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1912,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f1910])).

fof(f1913,plain,
    ( spl5_74
    | ~ spl5_26
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f1896,f1737,f532,f1910])).

fof(f532,plain,
    ( spl5_26
  <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1737,plain,
    ( spl5_62
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f1896,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_26
    | ~ spl5_62 ),
    inference(superposition,[],[f1590,f1739])).

fof(f1739,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f1737])).

fof(f1590,plain,
    ( ! [X7] : r1_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl5_26 ),
    inference(trivial_inequality_removal,[],[f1589])).

fof(f1589,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(sK0,sK1)) )
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f1588,f186])).

fof(f1588,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k4_xboole_0(X7,k2_xboole_0(sK2,X7))
        | r1_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(sK0,sK1)) )
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f1578,f31])).

fof(f1578,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k4_xboole_0(X7,k2_xboole_0(sK2,k4_xboole_0(X7,sK2)))
        | r1_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(sK0,sK1)) )
    | ~ spl5_26 ),
    inference(superposition,[],[f173,f534])).

fof(f534,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f532])).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 != k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))
      | r1_xboole_0(k4_xboole_0(X3,X4),X5) ) ),
    inference(forward_demodulation,[],[f162,f42])).

fof(f162,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k2_xboole_0(X4,X5)))
      | r1_xboole_0(k4_xboole_0(X3,X4),X5) ) ),
    inference(superposition,[],[f46,f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1746,plain,
    ( spl5_62
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f1745,f237,f1737])).

fof(f237,plain,
    ( spl5_15
  <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1745,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f1720,f525])).

fof(f525,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k4_xboole_0(X1,X0)) = X1 ),
    inference(forward_demodulation,[],[f524,f99])).

fof(f99,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f95,f26])).

fof(f95,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f524,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f510,f92])).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f32,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f510,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X0)) ),
    inference(superposition,[],[f164,f142])).

fof(f164,plain,(
    ! [X12,X10,X11] : k2_xboole_0(X12,k4_xboole_0(X10,X11)) = k2_xboole_0(X12,k4_xboole_0(X10,k2_xboole_0(X11,X12))) ),
    inference(superposition,[],[f31,f42])).

fof(f1720,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_15 ),
    inference(superposition,[],[f29,f239])).

fof(f239,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f237])).

fof(f1682,plain,
    ( spl5_39
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f1655,f1149,f867])).

fof(f867,plain,
    ( spl5_39
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f1655,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_45 ),
    inference(superposition,[],[f26,f1151])).

fof(f1151,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f1517,plain,
    ( spl5_1
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f1508,f867,f49])).

fof(f49,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1508,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_39 ),
    inference(trivial_inequality_removal,[],[f1491])).

fof(f1491,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl5_39 ),
    inference(superposition,[],[f41,f868])).

fof(f868,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f867])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f535,plain,
    ( spl5_26
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f530,f71,f532])).

fof(f71,plain,
    ( spl5_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f530,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f529,f102])).

fof(f102,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f99,f29])).

fof(f529,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f515,f29])).

fof(f515,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_5 ),
    inference(superposition,[],[f164,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f487,plain,
    ( spl5_15
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f486,f138,f237])).

fof(f138,plain,
    ( spl5_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f486,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f485,f26])).

fof(f485,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f466,f26])).

fof(f466,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),sK0),k1_xboole_0)
    | ~ spl5_10 ),
    inference(superposition,[],[f94,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f94,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f32,f31])).

fof(f301,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f300,f59,f71])).

fof(f59,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f300,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f61,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f299,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f298,f54,f138])).

fof(f54,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f298,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f45])).

fof(f56,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f22,f59])).

fof(f22,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f57,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (12839)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (12836)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (12841)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (12847)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (12855)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (12837)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (12833)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (12835)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (12854)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (12854)Refutation not found, incomplete strategy% (12854)------------------------------
% 0.20/0.53  % (12854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12854)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12854)Memory used [KB]: 10618
% 0.20/0.53  % (12854)Time elapsed: 0.088 s
% 0.20/0.53  % (12854)------------------------------
% 0.20/0.53  % (12854)------------------------------
% 0.20/0.53  % (12843)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (12861)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (12859)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (12852)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (12834)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (12858)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (12846)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (12838)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (12840)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (12842)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (12851)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (12850)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (12832)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (12860)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (12853)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (12849)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (12849)Refutation not found, incomplete strategy% (12849)------------------------------
% 0.20/0.55  % (12849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12849)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12849)Memory used [KB]: 10618
% 0.20/0.55  % (12849)Time elapsed: 0.148 s
% 0.20/0.55  % (12849)------------------------------
% 0.20/0.55  % (12849)------------------------------
% 0.20/0.55  % (12844)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (12845)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (12856)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (12857)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.60/0.57  % (12848)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.19/0.69  % (12863)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.69  % (12848)Refutation found. Thanks to Tanya!
% 2.19/0.69  % SZS status Theorem for theBenchmark
% 2.19/0.69  % SZS output start Proof for theBenchmark
% 2.19/0.69  fof(f1945,plain,(
% 2.19/0.69    $false),
% 2.19/0.69    inference(avatar_sat_refutation,[],[f52,f57,f62,f299,f301,f487,f535,f1517,f1682,f1746,f1913,f1922,f1944])).
% 2.19/0.69  fof(f1944,plain,(
% 2.19/0.69    spl5_45 | ~spl5_75),
% 2.19/0.69    inference(avatar_split_clause,[],[f1943,f1919,f1149])).
% 2.19/0.69  fof(f1149,plain,(
% 2.19/0.69    spl5_45 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 2.19/0.69  fof(f1919,plain,(
% 2.19/0.69    spl5_75 <=> r1_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 2.19/0.69  fof(f1943,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl5_75),
% 2.19/0.69    inference(forward_demodulation,[],[f1942,f186])).
% 2.19/0.69  fof(f186,plain,(
% 2.19/0.69    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.19/0.69    inference(forward_demodulation,[],[f178,f31])).
% 2.19/0.69  fof(f31,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.19/0.69    inference(cnf_transformation,[],[f6])).
% 2.19/0.69  fof(f6,axiom,(
% 2.19/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.19/0.69  fof(f178,plain,(
% 2.19/0.69    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 2.19/0.69    inference(superposition,[],[f142,f42])).
% 2.19/0.69  fof(f42,plain,(
% 2.19/0.69    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.19/0.69    inference(cnf_transformation,[],[f9])).
% 2.19/0.69  fof(f9,axiom,(
% 2.19/0.69    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.19/0.69  fof(f142,plain,(
% 2.19/0.69    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.19/0.69    inference(forward_demodulation,[],[f136,f26])).
% 2.19/0.69  fof(f26,plain,(
% 2.19/0.69    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.69    inference(cnf_transformation,[],[f7])).
% 2.19/0.69  fof(f7,axiom,(
% 2.19/0.69    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.19/0.69  fof(f136,plain,(
% 2.19/0.69    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.19/0.69    inference(resolution,[],[f45,f25])).
% 2.19/0.69  fof(f25,plain,(
% 2.19/0.69    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f11])).
% 2.19/0.69  fof(f11,axiom,(
% 2.19/0.69    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.19/0.69  fof(f45,plain,(
% 2.19/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.19/0.69    inference(definition_unfolding,[],[f39,f30])).
% 2.19/0.69  fof(f30,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.19/0.69    inference(cnf_transformation,[],[f10])).
% 2.19/0.69  fof(f10,axiom,(
% 2.19/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.19/0.69  fof(f39,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f2])).
% 2.19/0.69  fof(f2,axiom,(
% 2.19/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.19/0.69  fof(f1942,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) | ~spl5_75),
% 2.19/0.69    inference(forward_demodulation,[],[f1931,f42])).
% 2.19/0.69  fof(f1931,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | ~spl5_75),
% 2.19/0.69    inference(resolution,[],[f1921,f45])).
% 2.19/0.69  fof(f1921,plain,(
% 2.19/0.69    r1_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl5_75),
% 2.19/0.69    inference(avatar_component_clause,[],[f1919])).
% 2.19/0.69  fof(f1922,plain,(
% 2.19/0.69    spl5_75 | ~spl5_74),
% 2.19/0.69    inference(avatar_split_clause,[],[f1914,f1910,f1919])).
% 2.19/0.69  fof(f1910,plain,(
% 2.19/0.69    spl5_74 <=> r1_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 2.19/0.69  fof(f1914,plain,(
% 2.19/0.69    r1_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl5_74),
% 2.19/0.69    inference(resolution,[],[f1912,f417])).
% 2.19/0.69  fof(f417,plain,(
% 2.19/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.19/0.69    inference(duplicate_literal_removal,[],[f414])).
% 2.19/0.69  fof(f414,plain,(
% 2.19/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) | r1_xboole_0(X1,X0)) )),
% 2.19/0.69    inference(resolution,[],[f107,f36])).
% 2.19/0.69  fof(f36,plain,(
% 2.19/0.69    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f21])).
% 2.19/0.69  fof(f21,plain,(
% 2.19/0.69    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.19/0.69    inference(ennf_transformation,[],[f16])).
% 2.19/0.69  fof(f16,plain,(
% 2.19/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.69    inference(rectify,[],[f3])).
% 2.19/0.69  fof(f3,axiom,(
% 2.19/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.19/0.69  fof(f107,plain,(
% 2.19/0.69    ( ! [X4,X5,X3] : (~r2_hidden(sK4(X3,X4),X5) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X3,X4)) )),
% 2.19/0.69    inference(resolution,[],[f35,f37])).
% 2.19/0.69  fof(f37,plain,(
% 2.19/0.69    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f21])).
% 2.19/0.69  fof(f35,plain,(
% 2.19/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f21])).
% 2.19/0.69  fof(f1912,plain,(
% 2.19/0.69    r1_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_74),
% 2.19/0.69    inference(avatar_component_clause,[],[f1910])).
% 2.19/0.69  fof(f1913,plain,(
% 2.19/0.69    spl5_74 | ~spl5_26 | ~spl5_62),
% 2.19/0.69    inference(avatar_split_clause,[],[f1896,f1737,f532,f1910])).
% 2.19/0.69  fof(f532,plain,(
% 2.19/0.69    spl5_26 <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.19/0.69  fof(f1737,plain,(
% 2.19/0.69    spl5_62 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 2.19/0.69  fof(f1896,plain,(
% 2.19/0.69    r1_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl5_26 | ~spl5_62)),
% 2.19/0.69    inference(superposition,[],[f1590,f1739])).
% 2.19/0.69  fof(f1739,plain,(
% 2.19/0.69    sK0 = k4_xboole_0(sK0,sK2) | ~spl5_62),
% 2.19/0.69    inference(avatar_component_clause,[],[f1737])).
% 2.19/0.69  fof(f1590,plain,(
% 2.19/0.69    ( ! [X7] : (r1_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(sK0,sK1))) ) | ~spl5_26),
% 2.19/0.69    inference(trivial_inequality_removal,[],[f1589])).
% 2.19/0.69  fof(f1589,plain,(
% 2.19/0.69    ( ! [X7] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(sK0,sK1))) ) | ~spl5_26),
% 2.19/0.69    inference(forward_demodulation,[],[f1588,f186])).
% 2.19/0.69  fof(f1588,plain,(
% 2.19/0.69    ( ! [X7] : (k1_xboole_0 != k4_xboole_0(X7,k2_xboole_0(sK2,X7)) | r1_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(sK0,sK1))) ) | ~spl5_26),
% 2.19/0.69    inference(forward_demodulation,[],[f1578,f31])).
% 2.19/0.69  fof(f1578,plain,(
% 2.19/0.69    ( ! [X7] : (k1_xboole_0 != k4_xboole_0(X7,k2_xboole_0(sK2,k4_xboole_0(X7,sK2))) | r1_xboole_0(k4_xboole_0(X7,sK2),k4_xboole_0(sK0,sK1))) ) | ~spl5_26),
% 2.19/0.69    inference(superposition,[],[f173,f534])).
% 2.19/0.69  fof(f534,plain,(
% 2.19/0.69    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl5_26),
% 2.19/0.69    inference(avatar_component_clause,[],[f532])).
% 2.19/0.69  fof(f173,plain,(
% 2.19/0.69    ( ! [X4,X5,X3] : (k1_xboole_0 != k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) | r1_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 2.19/0.69    inference(forward_demodulation,[],[f162,f42])).
% 2.19/0.69  fof(f162,plain,(
% 2.19/0.69    ( ! [X4,X5,X3] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k2_xboole_0(X4,X5))) | r1_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 2.19/0.69    inference(superposition,[],[f46,f42])).
% 2.19/0.69  fof(f46,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.19/0.69    inference(definition_unfolding,[],[f38,f30])).
% 2.19/0.69  fof(f38,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f2])).
% 2.19/0.69  fof(f1746,plain,(
% 2.19/0.69    spl5_62 | ~spl5_15),
% 2.19/0.69    inference(avatar_split_clause,[],[f1745,f237,f1737])).
% 2.19/0.69  fof(f237,plain,(
% 2.19/0.69    spl5_15 <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.19/0.69  fof(f1745,plain,(
% 2.19/0.69    sK0 = k4_xboole_0(sK0,sK2) | ~spl5_15),
% 2.19/0.69    inference(forward_demodulation,[],[f1720,f525])).
% 2.19/0.69  fof(f525,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X0)) = X1) )),
% 2.19/0.69    inference(forward_demodulation,[],[f524,f99])).
% 2.19/0.69  fof(f99,plain,(
% 2.19/0.69    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.19/0.69    inference(forward_demodulation,[],[f95,f26])).
% 2.19/0.69  fof(f95,plain,(
% 2.19/0.69    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 2.19/0.69    inference(superposition,[],[f32,f26])).
% 2.19/0.69  fof(f32,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f8])).
% 2.19/0.69  fof(f8,axiom,(
% 2.19/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.19/0.69  fof(f524,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.19/0.69    inference(forward_demodulation,[],[f510,f92])).
% 2.19/0.69  fof(f92,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 2.19/0.69    inference(superposition,[],[f32,f29])).
% 2.19/0.69  fof(f29,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f1])).
% 2.19/0.69  fof(f1,axiom,(
% 2.19/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.19/0.69  fof(f510,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X0))) )),
% 2.19/0.69    inference(superposition,[],[f164,f142])).
% 2.19/0.69  fof(f164,plain,(
% 2.19/0.69    ( ! [X12,X10,X11] : (k2_xboole_0(X12,k4_xboole_0(X10,X11)) = k2_xboole_0(X12,k4_xboole_0(X10,k2_xboole_0(X11,X12)))) )),
% 2.19/0.69    inference(superposition,[],[f31,f42])).
% 2.19/0.69  fof(f1720,plain,(
% 2.19/0.69    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_15),
% 2.19/0.69    inference(superposition,[],[f29,f239])).
% 2.19/0.69  fof(f239,plain,(
% 2.19/0.69    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) | ~spl5_15),
% 2.19/0.69    inference(avatar_component_clause,[],[f237])).
% 2.19/0.69  fof(f1682,plain,(
% 2.19/0.69    spl5_39 | ~spl5_45),
% 2.19/0.69    inference(avatar_split_clause,[],[f1655,f1149,f867])).
% 2.19/0.69  fof(f867,plain,(
% 2.19/0.69    spl5_39 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.19/0.69  fof(f1655,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl5_45),
% 2.19/0.69    inference(superposition,[],[f26,f1151])).
% 2.19/0.69  fof(f1151,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl5_45),
% 2.19/0.69    inference(avatar_component_clause,[],[f1149])).
% 2.19/0.69  fof(f1517,plain,(
% 2.19/0.69    spl5_1 | ~spl5_39),
% 2.19/0.69    inference(avatar_split_clause,[],[f1508,f867,f49])).
% 2.19/0.69  fof(f49,plain,(
% 2.19/0.69    spl5_1 <=> r1_tarski(sK0,sK1)),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.19/0.69  fof(f1508,plain,(
% 2.19/0.69    r1_tarski(sK0,sK1) | ~spl5_39),
% 2.19/0.69    inference(trivial_inequality_removal,[],[f1491])).
% 2.19/0.69  fof(f1491,plain,(
% 2.19/0.69    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | ~spl5_39),
% 2.19/0.69    inference(superposition,[],[f41,f868])).
% 2.19/0.69  fof(f868,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl5_39),
% 2.19/0.69    inference(avatar_component_clause,[],[f867])).
% 2.19/0.69  fof(f41,plain,(
% 2.19/0.69    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f5])).
% 2.19/0.69  fof(f5,axiom,(
% 2.19/0.69    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.19/0.69  fof(f535,plain,(
% 2.19/0.69    spl5_26 | ~spl5_5),
% 2.19/0.69    inference(avatar_split_clause,[],[f530,f71,f532])).
% 2.19/0.69  fof(f71,plain,(
% 2.19/0.69    spl5_5 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.19/0.69  fof(f530,plain,(
% 2.19/0.69    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl5_5),
% 2.19/0.69    inference(forward_demodulation,[],[f529,f102])).
% 2.19/0.69  fof(f102,plain,(
% 2.19/0.69    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.19/0.69    inference(superposition,[],[f99,f29])).
% 2.19/0.69  fof(f529,plain,(
% 2.19/0.69    k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,sK2) | ~spl5_5),
% 2.19/0.69    inference(forward_demodulation,[],[f515,f29])).
% 2.19/0.69  fof(f515,plain,(
% 2.19/0.69    k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k1_xboole_0) | ~spl5_5),
% 2.19/0.69    inference(superposition,[],[f164,f73])).
% 2.19/0.69  fof(f73,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_5),
% 2.19/0.69    inference(avatar_component_clause,[],[f71])).
% 2.19/0.69  fof(f487,plain,(
% 2.19/0.69    spl5_15 | ~spl5_10),
% 2.19/0.69    inference(avatar_split_clause,[],[f486,f138,f237])).
% 2.19/0.69  fof(f138,plain,(
% 2.19/0.69    spl5_10 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.19/0.69  fof(f486,plain,(
% 2.19/0.69    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) | ~spl5_10),
% 2.19/0.69    inference(forward_demodulation,[],[f485,f26])).
% 2.19/0.69  fof(f485,plain,(
% 2.19/0.69    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) | ~spl5_10),
% 2.19/0.69    inference(forward_demodulation,[],[f466,f26])).
% 2.19/0.69  fof(f466,plain,(
% 2.19/0.69    k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),sK0),k1_xboole_0) | ~spl5_10),
% 2.19/0.69    inference(superposition,[],[f94,f140])).
% 2.19/0.69  fof(f140,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_10),
% 2.19/0.69    inference(avatar_component_clause,[],[f138])).
% 2.19/0.69  fof(f94,plain,(
% 2.19/0.69    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 2.19/0.69    inference(superposition,[],[f32,f31])).
% 2.19/0.69  fof(f301,plain,(
% 2.19/0.69    spl5_5 | ~spl5_3),
% 2.19/0.69    inference(avatar_split_clause,[],[f300,f59,f71])).
% 2.19/0.69  fof(f59,plain,(
% 2.19/0.69    spl5_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.19/0.69  fof(f300,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 2.19/0.69    inference(resolution,[],[f61,f40])).
% 2.19/0.69  fof(f40,plain,(
% 2.19/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.19/0.69    inference(cnf_transformation,[],[f5])).
% 2.19/0.69  fof(f61,plain,(
% 2.19/0.69    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 2.19/0.69    inference(avatar_component_clause,[],[f59])).
% 2.19/0.69  fof(f299,plain,(
% 2.19/0.69    spl5_10 | ~spl5_2),
% 2.19/0.69    inference(avatar_split_clause,[],[f298,f54,f138])).
% 2.19/0.69  fof(f54,plain,(
% 2.19/0.69    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 2.19/0.69    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.19/0.69  fof(f298,plain,(
% 2.19/0.69    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_2),
% 2.19/0.69    inference(resolution,[],[f56,f45])).
% 2.19/0.69  fof(f56,plain,(
% 2.19/0.69    r1_xboole_0(sK0,sK2) | ~spl5_2),
% 2.19/0.69    inference(avatar_component_clause,[],[f54])).
% 2.19/0.69  fof(f62,plain,(
% 2.19/0.69    spl5_3),
% 2.19/0.69    inference(avatar_split_clause,[],[f22,f59])).
% 2.19/0.69  fof(f22,plain,(
% 2.19/0.69    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.19/0.69    inference(cnf_transformation,[],[f18])).
% 2.19/0.69  fof(f18,plain,(
% 2.19/0.69    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.19/0.69    inference(flattening,[],[f17])).
% 2.19/0.69  fof(f17,plain,(
% 2.19/0.69    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.19/0.69    inference(ennf_transformation,[],[f14])).
% 2.19/0.69  fof(f14,negated_conjecture,(
% 2.19/0.69    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.19/0.69    inference(negated_conjecture,[],[f13])).
% 2.19/0.69  fof(f13,conjecture,(
% 2.19/0.69    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.19/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.19/0.69  fof(f57,plain,(
% 2.19/0.69    spl5_2),
% 2.19/0.69    inference(avatar_split_clause,[],[f23,f54])).
% 2.19/0.69  fof(f23,plain,(
% 2.19/0.69    r1_xboole_0(sK0,sK2)),
% 2.19/0.69    inference(cnf_transformation,[],[f18])).
% 2.19/0.69  fof(f52,plain,(
% 2.19/0.69    ~spl5_1),
% 2.19/0.69    inference(avatar_split_clause,[],[f24,f49])).
% 2.19/0.69  fof(f24,plain,(
% 2.19/0.69    ~r1_tarski(sK0,sK1)),
% 2.19/0.69    inference(cnf_transformation,[],[f18])).
% 2.19/0.69  % SZS output end Proof for theBenchmark
% 2.19/0.69  % (12848)------------------------------
% 2.19/0.69  % (12848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.69  % (12848)Termination reason: Refutation
% 2.19/0.69  
% 2.19/0.69  % (12848)Memory used [KB]: 11897
% 2.19/0.69  % (12848)Time elapsed: 0.262 s
% 2.19/0.69  % (12848)------------------------------
% 2.19/0.69  % (12848)------------------------------
% 2.19/0.70  % (12831)Success in time 0.339 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:31 EST 2020

% Result     : Theorem 8.16s
% Output     : Refutation 8.16s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 655 expanded)
%              Number of leaves         :   20 ( 188 expanded)
%              Depth                    :   20
%              Number of atoms          :  480 (1793 expanded)
%              Number of equality atoms :  162 ( 711 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26624)Termination reason: Time limit

% (26624)Memory used [KB]: 20468
% (26624)Time elapsed: 1.019 s
% (26624)------------------------------
% (26624)------------------------------
fof(f6515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f122,f139,f157,f2383,f2472,f2550,f4842,f6408,f6502])).

fof(f6502,plain,
    ( ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15
    | ~ spl15_24 ),
    inference(avatar_contradiction_clause,[],[f6501])).

fof(f6501,plain,
    ( $false
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15
    | ~ spl15_24 ),
    inference(subsumption_resolution,[],[f6446,f2683])).

fof(f2683,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl15_15 ),
    inference(resolution,[],[f2584,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2584,plain,
    ( ! [X8] : ~ r2_hidden(X8,k1_xboole_0)
    | ~ spl15_15 ),
    inference(forward_demodulation,[],[f2563,f82])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2563,plain,
    ( ! [X8] : ~ r2_hidden(X8,k2_zfmisc_1(k1_xboole_0,k2_mcart_1(X8)))
    | ~ spl15_15 ),
    inference(superposition,[],[f1485,f2382])).

fof(f2382,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f2380])).

fof(f2380,plain,
    ( spl15_15
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f1485,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_mcart_1(X0))) ),
    inference(resolution,[],[f49,f1452])).

fof(f1452,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f46,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f6446,plain,
    ( ! [X3] : ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X3),sK0))
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_24 ),
    inference(superposition,[],[f5419,f6407])).

fof(f6407,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl15_24 ),
    inference(avatar_component_clause,[],[f6405])).

fof(f6405,plain,
    ( spl15_24
  <=> k1_xboole_0 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).

fof(f5419,plain,
    ( ! [X2,X3] : ~ r1_tarski(k2_tarski(X2,sK0),k2_zfmisc_1(k1_tarski(X3),sK0))
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(forward_demodulation,[],[f1523,f170])).

fof(f170,plain,
    ( sK0 = sK2
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(backward_demodulation,[],[f138,f117])).

fof(f117,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl15_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f138,plain,
    ( sK2 = k2_mcart_1(sK0)
    | ~ spl15_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl15_5
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f1523,plain,
    ( ! [X2,X3] : ~ r1_tarski(k2_tarski(X2,sK0),k2_zfmisc_1(k1_tarski(X3),sK2))
    | ~ spl15_5 ),
    inference(resolution,[],[f1519,f1470])).

fof(f1470,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(X0,k2_zfmisc_1(k1_tarski(X1),sK2)) )
    | ~ spl15_5 ),
    inference(resolution,[],[f1466,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1466,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(k1_tarski(X0),sK2))
    | ~ spl15_5 ),
    inference(resolution,[],[f209,f1452])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2,X0)
        | ~ r2_hidden(sK0,k2_zfmisc_1(k1_tarski(X1),X0)) )
    | ~ spl15_5 ),
    inference(superposition,[],[f49,f138])).

fof(f1519,plain,(
    ! [X0,X1] : r2_hidden(X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f1512,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f1512,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(resolution,[],[f91,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] : sP14(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP14(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP14(X4,X2,X1,X0)
      | r2_hidden(X4,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP14(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6408,plain,
    ( spl15_24
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f6398,f2380,f136,f115,f96,f6405])).

fof(f96,plain,
    ( spl15_1
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f6398,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(equality_resolution,[],[f6392])).

fof(f6392,plain,
    ( ! [X21] :
        ( sK0 != X21
        | k1_xboole_0 = k2_tarski(X21,sK0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f6383,f1519])).

fof(f6383,plain,
    ( ! [X21] :
        ( sK0 != X21
        | ~ r2_hidden(sK0,k2_tarski(X21,sK0))
        | k1_xboole_0 = k2_tarski(X21,sK0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(duplicate_literal_removal,[],[f6382])).

fof(f6382,plain,
    ( ! [X21] :
        ( sK0 != X21
        | ~ r2_hidden(sK0,k2_tarski(X21,sK0))
        | k1_xboole_0 = k2_tarski(X21,sK0)
        | k1_xboole_0 = k2_tarski(X21,sK0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(superposition,[],[f5375,f5428])).

fof(f5428,plain,
    ( ! [X9] :
        ( sK5(k2_tarski(X9,sK0)) = X9
        | k1_xboole_0 = k2_tarski(X9,sK0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f5418,f1519])).

fof(f5418,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK0,k2_tarski(X9,sK0))
        | k1_xboole_0 = k2_tarski(X9,sK0)
        | sK5(k2_tarski(X9,sK0)) = X9 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(forward_demodulation,[],[f4482,f170])).

fof(f4482,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK2,k2_tarski(X9,sK0))
        | k1_xboole_0 = k2_tarski(X9,sK0)
        | sK5(k2_tarski(X9,sK0)) = X9 )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(trivial_inequality_removal,[],[f4468])).

fof(f4468,plain,
    ( ! [X9] :
        ( sK0 != sK0
        | ~ r2_hidden(sK2,k2_tarski(X9,sK0))
        | k1_xboole_0 = k2_tarski(X9,sK0)
        | sK5(k2_tarski(X9,sK0)) = X9 )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(superposition,[],[f101,f4385])).

fof(f4385,plain,
    ( ! [X0] :
        ( sK0 = sK5(k2_tarski(X0,sK0))
        | sK5(k2_tarski(X0,sK0)) = X0 )
    | ~ spl15_5
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f4363,f2683])).

fof(f4363,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X1),sK2))
        | sK5(k2_tarski(X0,sK0)) = X0
        | sK0 = sK5(k2_tarski(X0,sK0)) )
    | ~ spl15_5 ),
    inference(superposition,[],[f1523,f1629])).

fof(f1629,plain,(
    ! [X10,X11] :
      ( k1_xboole_0 = k2_tarski(X10,X11)
      | sK5(k2_tarski(X10,X11)) = X10
      | sK5(k2_tarski(X10,X11)) = X11 ) ),
    inference(resolution,[],[f1465,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f1465,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
      | X0 = X2
      | X0 = X1 ) ),
    inference(resolution,[],[f83,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f101,plain,
    ( ! [X1] :
        ( sK0 != sK5(X1)
        | ~ r2_hidden(sK2,X1)
        | k1_xboole_0 = X1 )
    | ~ spl15_1 ),
    inference(superposition,[],[f32,f98])).

fof(f98,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5375,plain,
    ( ! [X1] :
        ( sK0 != sK5(X1)
        | ~ r2_hidden(sK0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(forward_demodulation,[],[f101,f170])).

fof(f4842,plain,
    ( ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(avatar_contradiction_clause,[],[f4841])).

fof(f4841,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f4654,f2683])).

fof(f4654,plain,
    ( ! [X33] : ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X33),sK2))
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(trivial_inequality_removal,[],[f4649])).

fof(f4649,plain,
    ( ! [X33] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X33),sK2))
        | sK0 != sK0 )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(superposition,[],[f1540,f4566])).

fof(f4566,plain,
    ( ! [X19] :
        ( k1_xboole_0 = k2_tarski(X19,sK0)
        | sK0 != X19 )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f4561,f1519])).

fof(f4561,plain,
    ( ! [X19] :
        ( sK0 != X19
        | ~ r2_hidden(sK0,k2_tarski(X19,sK0))
        | k1_xboole_0 = k2_tarski(X19,sK0) )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(superposition,[],[f2646,f4524])).

fof(f4524,plain,
    ( ! [X1] : sK5(k2_tarski(X1,sK0)) = X1
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f4501,f2683])).

fof(f4501,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X2),sK2))
        | sK5(k2_tarski(X1,sK0)) = X1 )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(superposition,[],[f1523,f4483])).

fof(f4483,plain,
    ( ! [X18] :
        ( k1_xboole_0 = k2_tarski(X18,sK0)
        | sK5(k2_tarski(X18,sK0)) = X18 )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f4481,f1519])).

fof(f4481,plain,
    ( ! [X18] :
        ( ~ r2_hidden(sK0,k2_tarski(X18,sK0))
        | k1_xboole_0 = k2_tarski(X18,sK0)
        | sK5(k2_tarski(X18,sK0)) = X18 )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(trivial_inequality_removal,[],[f4471])).

fof(f4471,plain,
    ( ! [X18] :
        ( sK0 != sK0
        | ~ r2_hidden(sK0,k2_tarski(X18,sK0))
        | k1_xboole_0 = k2_tarski(X18,sK0)
        | sK5(k2_tarski(X18,sK0)) = X18 )
    | ~ spl15_1
    | ~ spl15_5
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_16 ),
    inference(superposition,[],[f2646,f4385])).

fof(f2646,plain,
    ( ! [X0] :
        ( sK0 != sK5(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_16 ),
    inference(backward_demodulation,[],[f100,f2644])).

fof(f2644,plain,
    ( sK0 = sK1
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_16 ),
    inference(backward_demodulation,[],[f2471,f201])).

fof(f201,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(backward_demodulation,[],[f102,f182])).

fof(f182,plain,
    ( sK0 = sK1
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(forward_demodulation,[],[f102,f156])).

fof(f156,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl15_6
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f102,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl15_1 ),
    inference(superposition,[],[f35,f98])).

fof(f35,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f2471,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f2469])).

fof(f2469,plain,
    ( spl15_16
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f100,plain,
    ( ! [X0] :
        ( sK0 != sK5(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl15_1 ),
    inference(superposition,[],[f31,f98])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1540,plain,
    ( ! [X2,X3] : ~ r1_tarski(k2_tarski(sK0,X2),k2_zfmisc_1(k1_tarski(X3),sK2))
    | ~ spl15_5 ),
    inference(resolution,[],[f1536,f1470])).

fof(f1536,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f1513,f34])).

fof(f1513,plain,(
    ! [X4,X5,X3] : r2_hidden(X3,k1_enumset1(X4,X3,X5)) ),
    inference(resolution,[],[f91,f93])).

fof(f93,plain,(
    ! [X4,X2,X0] : sP14(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP14(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2550,plain,
    ( spl15_15
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(avatar_split_clause,[],[f2545,f136,f115,f96,f2380])).

fof(f2545,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(duplicate_literal_removal,[],[f2543])).

fof(f2543,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(resolution,[],[f2435,f2299])).

fof(f2299,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_tarski(X6))
      | k1_xboole_0 = k1_tarski(X6) ) ),
    inference(duplicate_literal_removal,[],[f2286])).

fof(f2286,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_tarski(X6))
      | k1_xboole_0 = k1_tarski(X6)
      | k1_xboole_0 = k1_tarski(X6) ) ),
    inference(superposition,[],[f33,f1670])).

fof(f1670,plain,(
    ! [X2] :
      ( sK5(k1_tarski(X2)) = X2
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(resolution,[],[f1666,f33])).

fof(f1666,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(condensation,[],[f1665])).

fof(f1665,plain,(
    ! [X6,X4,X7,X5] :
      ( X4 = X5
      | ~ r2_hidden(X4,k1_tarski(X5))
      | ~ r2_hidden(X6,X7) ) ),
    inference(forward_demodulation,[],[f1658,f35])).

fof(f1658,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k1_tarski(X5))
      | ~ r2_hidden(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X6)) = X5 ) ),
    inference(resolution,[],[f1525,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1525,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1))
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f89,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ sP10(X3,X1,X0)
      | r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP10(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f89,plain,(
    ! [X4,X0,X5,X1] :
      ( sP10(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP10(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2435,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK0,k1_tarski(X7))
        | k1_xboole_0 = k1_tarski(X7) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(subsumption_resolution,[],[f2422,f1666])).

fof(f2422,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK0,k1_tarski(X7))
        | sK0 != X7
        | k1_xboole_0 = k1_tarski(X7) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_5 ),
    inference(backward_demodulation,[],[f2298,f170])).

fof(f2298,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK2,k1_tarski(X7))
        | sK0 != X7
        | k1_xboole_0 = k1_tarski(X7) )
    | ~ spl15_1 ),
    inference(duplicate_literal_removal,[],[f2287])).

fof(f2287,plain,
    ( ! [X7] :
        ( sK0 != X7
        | ~ r2_hidden(sK2,k1_tarski(X7))
        | k1_xboole_0 = k1_tarski(X7)
        | k1_xboole_0 = k1_tarski(X7) )
    | ~ spl15_1 ),
    inference(superposition,[],[f101,f1670])).

fof(f2472,plain,
    ( spl15_16
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f102,f96,f2469])).

fof(f2383,plain,
    ( spl15_15
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f2329,f154,f96,f2380])).

fof(f2329,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(duplicate_literal_removal,[],[f2322])).

fof(f2322,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | k1_xboole_0 = k1_tarski(sK0)
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(resolution,[],[f2299,f2302])).

fof(f2302,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK0,k1_tarski(X8))
        | k1_xboole_0 = k1_tarski(X8) )
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f2297,f1666])).

fof(f2297,plain,
    ( ! [X8] :
        ( sK0 != X8
        | ~ r2_hidden(sK0,k1_tarski(X8))
        | k1_xboole_0 = k1_tarski(X8) )
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(duplicate_literal_removal,[],[f2288])).

fof(f2288,plain,
    ( ! [X8] :
        ( sK0 != X8
        | ~ r2_hidden(sK0,k1_tarski(X8))
        | k1_xboole_0 = k1_tarski(X8)
        | k1_xboole_0 = k1_tarski(X8) )
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(superposition,[],[f200,f1670])).

fof(f200,plain,
    ( ! [X0] :
        ( sK0 != sK5(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl15_1
    | ~ spl15_6 ),
    inference(backward_demodulation,[],[f100,f182])).

fof(f157,plain,
    ( spl15_6
    | ~ spl15_1
    | ~ spl15_3 ),
    inference(avatar_split_clause,[],[f125,f119,f96,f154])).

fof(f119,plain,
    ( spl15_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f125,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl15_1
    | ~ spl15_3 ),
    inference(backward_demodulation,[],[f102,f121])).

fof(f121,plain,
    ( sK0 = sK1
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f139,plain,
    ( spl15_5
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f103,f96,f136])).

fof(f103,plain,
    ( sK2 = k2_mcart_1(sK0)
    | ~ spl15_1 ),
    inference(superposition,[],[f36,f98])).

fof(f36,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f122,plain,
    ( spl15_2
    | spl15_3
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f109,f96,f119,f115])).

fof(f109,plain,
    ( sK0 = sK1
    | sK0 = k2_mcart_1(sK0)
    | ~ spl15_1 ),
    inference(backward_demodulation,[],[f26,f102])).

fof(f26,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f99,plain,(
    spl15_1 ),
    inference(avatar_split_clause,[],[f27,f96])).

fof(f27,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (26623)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (26644)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.16/0.51  % (26636)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.16/0.51  % (26628)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.52  % (26633)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.16/0.52  % (26632)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.16/0.52  % (26645)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.16/0.52  % (26622)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.16/0.52  % (26651)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.16/0.52  % (26622)Refutation not found, incomplete strategy% (26622)------------------------------
% 1.16/0.52  % (26622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (26622)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.52  
% 1.16/0.52  % (26622)Memory used [KB]: 1791
% 1.16/0.52  % (26622)Time elapsed: 0.117 s
% 1.16/0.52  % (26622)------------------------------
% 1.16/0.52  % (26622)------------------------------
% 1.16/0.52  % (26637)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.16/0.52  % (26637)Refutation not found, incomplete strategy% (26637)------------------------------
% 1.16/0.52  % (26637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (26629)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.53  % (26649)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.53  % (26635)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.53  % (26650)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.53  % (26643)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.53  % (26624)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (26641)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.53  % (26638)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.53  % (26647)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.53  % (26626)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (26625)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (26630)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.53  % (26637)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (26637)Memory used [KB]: 6268
% 1.29/0.53  % (26637)Time elapsed: 0.004 s
% 1.29/0.53  % (26637)------------------------------
% 1.29/0.53  % (26637)------------------------------
% 1.29/0.54  % (26631)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (26639)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.54  % (26639)Refutation not found, incomplete strategy% (26639)------------------------------
% 1.29/0.54  % (26639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26639)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (26639)Memory used [KB]: 10618
% 1.29/0.54  % (26639)Time elapsed: 0.128 s
% 1.29/0.54  % (26639)------------------------------
% 1.29/0.54  % (26639)------------------------------
% 1.29/0.54  % (26632)Refutation not found, incomplete strategy% (26632)------------------------------
% 1.29/0.54  % (26632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26632)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (26632)Memory used [KB]: 10746
% 1.29/0.54  % (26632)Time elapsed: 0.118 s
% 1.29/0.54  % (26632)------------------------------
% 1.29/0.54  % (26632)------------------------------
% 1.29/0.54  % (26646)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (26633)Refutation not found, incomplete strategy% (26633)------------------------------
% 1.29/0.55  % (26633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (26633)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (26633)Memory used [KB]: 10874
% 1.29/0.55  % (26633)Time elapsed: 0.143 s
% 1.29/0.55  % (26633)------------------------------
% 1.29/0.55  % (26633)------------------------------
% 1.29/0.56  % (26648)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.56  % (26627)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.57  % (26642)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.57  % (26640)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.57  % (26634)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.48/0.70  % (26655)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.48/0.70  % (26655)Refutation not found, incomplete strategy% (26655)------------------------------
% 2.48/0.70  % (26655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.48/0.70  % (26655)Termination reason: Refutation not found, incomplete strategy
% 2.48/0.70  
% 2.48/0.70  % (26655)Memory used [KB]: 6268
% 2.48/0.70  % (26655)Time elapsed: 0.140 s
% 2.48/0.70  % (26655)------------------------------
% 2.48/0.70  % (26655)------------------------------
% 2.48/0.73  % (26656)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.48/0.74  % (26669)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.48/0.76  % (26668)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.01/0.77  % (26660)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.01/0.79  % (26669)Refutation not found, incomplete strategy% (26669)------------------------------
% 3.01/0.79  % (26669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.79  % (26669)Termination reason: Refutation not found, incomplete strategy
% 3.01/0.79  
% 3.01/0.79  % (26669)Memory used [KB]: 11001
% 3.01/0.79  % (26669)Time elapsed: 0.174 s
% 3.01/0.79  % (26669)------------------------------
% 3.01/0.79  % (26669)------------------------------
% 3.43/0.85  % (26627)Time limit reached!
% 3.43/0.85  % (26627)------------------------------
% 3.43/0.85  % (26627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.43/0.85  % (26627)Termination reason: Time limit
% 3.43/0.85  
% 3.43/0.85  % (26627)Memory used [KB]: 10106
% 3.43/0.85  % (26627)Time elapsed: 0.423 s
% 3.43/0.85  % (26627)------------------------------
% 3.43/0.85  % (26627)------------------------------
% 3.43/0.86  % (26686)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.43/0.91  % (26623)Time limit reached!
% 3.43/0.91  % (26623)------------------------------
% 3.43/0.91  % (26623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.93  % (26692)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.07/0.93  % (26623)Termination reason: Time limit
% 4.07/0.93  % (26623)Termination phase: Saturation
% 4.07/0.93  
% 4.07/0.93  % (26623)Memory used [KB]: 9338
% 4.07/0.93  % (26623)Time elapsed: 0.500 s
% 4.07/0.93  % (26623)------------------------------
% 4.07/0.93  % (26623)------------------------------
% 4.07/0.94  % (26634)Time limit reached!
% 4.07/0.94  % (26634)------------------------------
% 4.07/0.94  % (26634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.94  % (26634)Termination reason: Time limit
% 4.07/0.94  % (26634)Termination phase: Saturation
% 4.07/0.94  
% 4.07/0.94  % (26634)Memory used [KB]: 8699
% 4.07/0.94  % (26634)Time elapsed: 0.500 s
% 4.07/0.94  % (26634)------------------------------
% 4.07/0.94  % (26634)------------------------------
% 4.07/0.97  % (26693)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.50/1.00  % (26668)Time limit reached!
% 4.50/1.00  % (26668)------------------------------
% 4.50/1.00  % (26668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.00  % (26668)Termination reason: Time limit
% 4.50/1.00  % (26668)Termination phase: Saturation
% 4.50/1.00  
% 4.50/1.00  % (26668)Memory used [KB]: 7291
% 4.50/1.00  % (26668)Time elapsed: 0.402 s
% 4.50/1.00  % (26668)------------------------------
% 4.50/1.00  % (26668)------------------------------
% 4.50/1.01  % (26638)Time limit reached!
% 4.50/1.01  % (26638)------------------------------
% 4.50/1.01  % (26638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.01  % (26638)Termination reason: Time limit
% 4.50/1.01  
% 4.50/1.01  % (26638)Memory used [KB]: 13944
% 4.50/1.01  % (26638)Time elapsed: 0.612 s
% 4.50/1.01  % (26638)------------------------------
% 4.50/1.01  % (26638)------------------------------
% 4.50/1.03  % (26629)Time limit reached!
% 4.50/1.03  % (26629)------------------------------
% 4.50/1.03  % (26629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.04  % (26650)Time limit reached!
% 4.50/1.04  % (26650)------------------------------
% 4.50/1.04  % (26650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/1.04  % (26629)Termination reason: Time limit
% 4.50/1.04  % (26629)Termination phase: Saturation
% 4.50/1.04  
% 4.50/1.04  % (26629)Memory used [KB]: 9850
% 4.50/1.04  % (26629)Time elapsed: 0.600 s
% 4.50/1.04  % (26629)------------------------------
% 4.50/1.04  % (26629)------------------------------
% 4.50/1.04  % (26650)Termination reason: Time limit
% 4.50/1.04  
% 4.50/1.04  % (26650)Memory used [KB]: 8955
% 4.50/1.04  % (26650)Time elapsed: 0.607 s
% 4.50/1.04  % (26650)------------------------------
% 4.50/1.04  % (26650)------------------------------
% 4.50/1.05  % (26694)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.04/1.07  % (26695)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.11/1.14  % (26697)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.11/1.14  % (26696)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.11/1.17  % (26698)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.11/1.18  % (26699)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.11/1.19  % (26699)Refutation not found, incomplete strategy% (26699)------------------------------
% 6.11/1.19  % (26699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.11/1.19  % (26699)Termination reason: Refutation not found, incomplete strategy
% 6.11/1.19  
% 6.11/1.19  % (26699)Memory used [KB]: 1791
% 6.11/1.19  % (26699)Time elapsed: 0.094 s
% 6.11/1.19  % (26699)------------------------------
% 6.11/1.19  % (26699)------------------------------
% 6.11/1.20  % (26643)Time limit reached!
% 6.11/1.20  % (26643)------------------------------
% 6.11/1.20  % (26643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.11/1.20  % (26643)Termination reason: Time limit
% 6.11/1.20  
% 6.11/1.20  % (26643)Memory used [KB]: 3582
% 6.11/1.20  % (26643)Time elapsed: 0.802 s
% 6.11/1.20  % (26643)------------------------------
% 6.11/1.20  % (26643)------------------------------
% 7.24/1.32  % (26728)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 7.24/1.33  % (26737)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 8.16/1.42  % (26624)Time limit reached!
% 8.16/1.42  % (26624)------------------------------
% 8.16/1.42  % (26624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.16/1.43  % (26642)Refutation found. Thanks to Tanya!
% 8.16/1.43  % SZS status Theorem for theBenchmark
% 8.16/1.43  % SZS output start Proof for theBenchmark
% 8.16/1.43  % (26624)Termination reason: Time limit
% 8.16/1.43  
% 8.16/1.43  % (26624)Memory used [KB]: 20468
% 8.16/1.43  % (26624)Time elapsed: 1.019 s
% 8.16/1.43  % (26624)------------------------------
% 8.16/1.43  % (26624)------------------------------
% 8.16/1.43  fof(f6515,plain,(
% 8.16/1.43    $false),
% 8.16/1.43    inference(avatar_sat_refutation,[],[f99,f122,f139,f157,f2383,f2472,f2550,f4842,f6408,f6502])).
% 8.16/1.43  fof(f6502,plain,(
% 8.16/1.43    ~spl15_2 | ~spl15_5 | ~spl15_15 | ~spl15_24),
% 8.16/1.43    inference(avatar_contradiction_clause,[],[f6501])).
% 8.16/1.43  fof(f6501,plain,(
% 8.16/1.43    $false | (~spl15_2 | ~spl15_5 | ~spl15_15 | ~spl15_24)),
% 8.16/1.43    inference(subsumption_resolution,[],[f6446,f2683])).
% 8.16/1.43  fof(f2683,plain,(
% 8.16/1.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl15_15),
% 8.16/1.43    inference(resolution,[],[f2584,f41])).
% 8.16/1.43  fof(f41,plain,(
% 8.16/1.43    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 8.16/1.43    inference(cnf_transformation,[],[f22])).
% 8.16/1.43  fof(f22,plain,(
% 8.16/1.43    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.16/1.43    inference(ennf_transformation,[],[f1])).
% 8.16/1.43  fof(f1,axiom,(
% 8.16/1.43    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 8.16/1.43  fof(f2584,plain,(
% 8.16/1.43    ( ! [X8] : (~r2_hidden(X8,k1_xboole_0)) ) | ~spl15_15),
% 8.16/1.43    inference(forward_demodulation,[],[f2563,f82])).
% 8.16/1.43  fof(f82,plain,(
% 8.16/1.43    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 8.16/1.43    inference(equality_resolution,[],[f44])).
% 8.16/1.43  fof(f44,plain,(
% 8.16/1.43    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 8.16/1.43    inference(cnf_transformation,[],[f10])).
% 8.16/1.43  fof(f10,axiom,(
% 8.16/1.43    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 8.16/1.43  fof(f2563,plain,(
% 8.16/1.43    ( ! [X8] : (~r2_hidden(X8,k2_zfmisc_1(k1_xboole_0,k2_mcart_1(X8)))) ) | ~spl15_15),
% 8.16/1.43    inference(superposition,[],[f1485,f2382])).
% 8.16/1.43  fof(f2382,plain,(
% 8.16/1.43    k1_xboole_0 = k1_tarski(sK0) | ~spl15_15),
% 8.16/1.43    inference(avatar_component_clause,[],[f2380])).
% 8.16/1.43  fof(f2380,plain,(
% 8.16/1.43    spl15_15 <=> k1_xboole_0 = k1_tarski(sK0)),
% 8.16/1.43    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).
% 8.16/1.43  fof(f1485,plain,(
% 8.16/1.43    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_mcart_1(X0)))) )),
% 8.16/1.43    inference(resolution,[],[f49,f1452])).
% 8.16/1.43  fof(f1452,plain,(
% 8.16/1.43    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 8.16/1.43    inference(resolution,[],[f46,f80])).
% 8.16/1.43  fof(f80,plain,(
% 8.16/1.43    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.16/1.43    inference(equality_resolution,[],[f37])).
% 8.16/1.43  fof(f37,plain,(
% 8.16/1.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 8.16/1.43    inference(cnf_transformation,[],[f2])).
% 8.16/1.43  fof(f2,axiom,(
% 8.16/1.43    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 8.16/1.43  fof(f46,plain,(
% 8.16/1.43    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 8.16/1.43    inference(cnf_transformation,[],[f23])).
% 8.16/1.43  fof(f23,plain,(
% 8.16/1.43    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 8.16/1.43    inference(ennf_transformation,[],[f11])).
% 8.16/1.43  fof(f11,axiom,(
% 8.16/1.43    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 8.16/1.43  fof(f49,plain,(
% 8.16/1.43    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 8.16/1.43    inference(cnf_transformation,[],[f24])).
% 8.16/1.43  fof(f24,plain,(
% 8.16/1.43    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 8.16/1.43    inference(ennf_transformation,[],[f13])).
% 8.16/1.43  fof(f13,axiom,(
% 8.16/1.43    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 8.16/1.43  fof(f6446,plain,(
% 8.16/1.43    ( ! [X3] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X3),sK0))) ) | (~spl15_2 | ~spl15_5 | ~spl15_24)),
% 8.16/1.43    inference(superposition,[],[f5419,f6407])).
% 8.16/1.43  fof(f6407,plain,(
% 8.16/1.43    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl15_24),
% 8.16/1.43    inference(avatar_component_clause,[],[f6405])).
% 8.16/1.43  fof(f6405,plain,(
% 8.16/1.43    spl15_24 <=> k1_xboole_0 = k2_tarski(sK0,sK0)),
% 8.16/1.43    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).
% 8.16/1.43  fof(f5419,plain,(
% 8.16/1.43    ( ! [X2,X3] : (~r1_tarski(k2_tarski(X2,sK0),k2_zfmisc_1(k1_tarski(X3),sK0))) ) | (~spl15_2 | ~spl15_5)),
% 8.16/1.43    inference(forward_demodulation,[],[f1523,f170])).
% 8.16/1.43  fof(f170,plain,(
% 8.16/1.43    sK0 = sK2 | (~spl15_2 | ~spl15_5)),
% 8.16/1.43    inference(backward_demodulation,[],[f138,f117])).
% 8.16/1.43  fof(f117,plain,(
% 8.16/1.43    sK0 = k2_mcart_1(sK0) | ~spl15_2),
% 8.16/1.43    inference(avatar_component_clause,[],[f115])).
% 8.16/1.43  fof(f115,plain,(
% 8.16/1.43    spl15_2 <=> sK0 = k2_mcart_1(sK0)),
% 8.16/1.43    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 8.16/1.43  fof(f138,plain,(
% 8.16/1.43    sK2 = k2_mcart_1(sK0) | ~spl15_5),
% 8.16/1.43    inference(avatar_component_clause,[],[f136])).
% 8.16/1.43  fof(f136,plain,(
% 8.16/1.43    spl15_5 <=> sK2 = k2_mcart_1(sK0)),
% 8.16/1.43    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).
% 8.16/1.43  fof(f1523,plain,(
% 8.16/1.43    ( ! [X2,X3] : (~r1_tarski(k2_tarski(X2,sK0),k2_zfmisc_1(k1_tarski(X3),sK2))) ) | ~spl15_5),
% 8.16/1.43    inference(resolution,[],[f1519,f1470])).
% 8.16/1.43  fof(f1470,plain,(
% 8.16/1.43    ( ! [X0,X1] : (~r2_hidden(sK0,X0) | ~r1_tarski(X0,k2_zfmisc_1(k1_tarski(X1),sK2))) ) | ~spl15_5),
% 8.16/1.43    inference(resolution,[],[f1466,f40])).
% 8.16/1.43  fof(f40,plain,(
% 8.16/1.43    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 8.16/1.43    inference(cnf_transformation,[],[f22])).
% 8.16/1.43  fof(f1466,plain,(
% 8.16/1.43    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(k1_tarski(X0),sK2))) ) | ~spl15_5),
% 8.16/1.43    inference(resolution,[],[f209,f1452])).
% 8.16/1.43  fof(f209,plain,(
% 8.16/1.43    ( ! [X0,X1] : (r2_hidden(sK2,X0) | ~r2_hidden(sK0,k2_zfmisc_1(k1_tarski(X1),X0))) ) | ~spl15_5),
% 8.16/1.43    inference(superposition,[],[f49,f138])).
% 8.16/1.43  fof(f1519,plain,(
% 8.16/1.43    ( ! [X0,X1] : (r2_hidden(X1,k2_tarski(X0,X1))) )),
% 8.16/1.43    inference(superposition,[],[f1512,f34])).
% 8.16/1.43  fof(f34,plain,(
% 8.16/1.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.16/1.43    inference(cnf_transformation,[],[f5])).
% 8.16/1.43  fof(f5,axiom,(
% 8.16/1.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 8.16/1.43  fof(f1512,plain,(
% 8.16/1.43    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X1,X2,X0))) )),
% 8.16/1.43    inference(resolution,[],[f91,f92])).
% 8.16/1.43  fof(f92,plain,(
% 8.16/1.43    ( ! [X4,X0,X1] : (sP14(X4,X4,X1,X0)) )),
% 8.16/1.43    inference(equality_resolution,[],[f68])).
% 8.16/1.43  fof(f68,plain,(
% 8.16/1.43    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP14(X4,X2,X1,X0)) )),
% 8.16/1.43    inference(cnf_transformation,[],[f25])).
% 8.16/1.43  fof(f25,plain,(
% 8.16/1.43    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 8.16/1.43    inference(ennf_transformation,[],[f3])).
% 8.16/1.43  fof(f3,axiom,(
% 8.16/1.43    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 8.16/1.43  fof(f91,plain,(
% 8.16/1.43    ( ! [X4,X2,X0,X1] : (~sP14(X4,X2,X1,X0) | r2_hidden(X4,k1_enumset1(X0,X1,X2))) )),
% 8.16/1.43    inference(equality_resolution,[],[f70])).
% 8.16/1.43  fof(f70,plain,(
% 8.16/1.43    ( ! [X4,X2,X0,X3,X1] : (~sP14(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 8.16/1.43    inference(cnf_transformation,[],[f25])).
% 8.16/1.43  fof(f6408,plain,(
% 8.16/1.43    spl15_24 | ~spl15_1 | ~spl15_2 | ~spl15_5 | ~spl15_15),
% 8.16/1.43    inference(avatar_split_clause,[],[f6398,f2380,f136,f115,f96,f6405])).
% 8.16/1.43  fof(f96,plain,(
% 8.16/1.43    spl15_1 <=> sK0 = k4_tarski(sK1,sK2)),
% 8.16/1.43    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 8.16/1.43  fof(f6398,plain,(
% 8.16/1.43    k1_xboole_0 = k2_tarski(sK0,sK0) | (~spl15_1 | ~spl15_2 | ~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(equality_resolution,[],[f6392])).
% 8.16/1.43  fof(f6392,plain,(
% 8.16/1.43    ( ! [X21] : (sK0 != X21 | k1_xboole_0 = k2_tarski(X21,sK0)) ) | (~spl15_1 | ~spl15_2 | ~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(subsumption_resolution,[],[f6383,f1519])).
% 8.16/1.43  fof(f6383,plain,(
% 8.16/1.43    ( ! [X21] : (sK0 != X21 | ~r2_hidden(sK0,k2_tarski(X21,sK0)) | k1_xboole_0 = k2_tarski(X21,sK0)) ) | (~spl15_1 | ~spl15_2 | ~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(duplicate_literal_removal,[],[f6382])).
% 8.16/1.43  fof(f6382,plain,(
% 8.16/1.43    ( ! [X21] : (sK0 != X21 | ~r2_hidden(sK0,k2_tarski(X21,sK0)) | k1_xboole_0 = k2_tarski(X21,sK0) | k1_xboole_0 = k2_tarski(X21,sK0)) ) | (~spl15_1 | ~spl15_2 | ~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(superposition,[],[f5375,f5428])).
% 8.16/1.43  fof(f5428,plain,(
% 8.16/1.43    ( ! [X9] : (sK5(k2_tarski(X9,sK0)) = X9 | k1_xboole_0 = k2_tarski(X9,sK0)) ) | (~spl15_1 | ~spl15_2 | ~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(subsumption_resolution,[],[f5418,f1519])).
% 8.16/1.43  fof(f5418,plain,(
% 8.16/1.43    ( ! [X9] : (~r2_hidden(sK0,k2_tarski(X9,sK0)) | k1_xboole_0 = k2_tarski(X9,sK0) | sK5(k2_tarski(X9,sK0)) = X9) ) | (~spl15_1 | ~spl15_2 | ~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(forward_demodulation,[],[f4482,f170])).
% 8.16/1.43  fof(f4482,plain,(
% 8.16/1.43    ( ! [X9] : (~r2_hidden(sK2,k2_tarski(X9,sK0)) | k1_xboole_0 = k2_tarski(X9,sK0) | sK5(k2_tarski(X9,sK0)) = X9) ) | (~spl15_1 | ~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(trivial_inequality_removal,[],[f4468])).
% 8.16/1.43  fof(f4468,plain,(
% 8.16/1.43    ( ! [X9] : (sK0 != sK0 | ~r2_hidden(sK2,k2_tarski(X9,sK0)) | k1_xboole_0 = k2_tarski(X9,sK0) | sK5(k2_tarski(X9,sK0)) = X9) ) | (~spl15_1 | ~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(superposition,[],[f101,f4385])).
% 8.16/1.43  fof(f4385,plain,(
% 8.16/1.43    ( ! [X0] : (sK0 = sK5(k2_tarski(X0,sK0)) | sK5(k2_tarski(X0,sK0)) = X0) ) | (~spl15_5 | ~spl15_15)),
% 8.16/1.43    inference(subsumption_resolution,[],[f4363,f2683])).
% 8.16/1.43  fof(f4363,plain,(
% 8.16/1.43    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X1),sK2)) | sK5(k2_tarski(X0,sK0)) = X0 | sK0 = sK5(k2_tarski(X0,sK0))) ) | ~spl15_5),
% 8.16/1.43    inference(superposition,[],[f1523,f1629])).
% 8.16/1.43  fof(f1629,plain,(
% 8.16/1.43    ( ! [X10,X11] : (k1_xboole_0 = k2_tarski(X10,X11) | sK5(k2_tarski(X10,X11)) = X10 | sK5(k2_tarski(X10,X11)) = X11) )),
% 8.16/1.43    inference(resolution,[],[f1465,f33])).
% 8.16/1.43  fof(f33,plain,(
% 8.16/1.43    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 8.16/1.43    inference(cnf_transformation,[],[f21])).
% 8.16/1.43  fof(f21,plain,(
% 8.16/1.43    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 8.16/1.43    inference(ennf_transformation,[],[f15])).
% 8.16/1.43  fof(f15,axiom,(
% 8.16/1.43    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 8.16/1.43  fof(f1465,plain,(
% 8.16/1.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X2 | X0 = X1) )),
% 8.16/1.43    inference(resolution,[],[f83,f52])).
% 8.16/1.43  fof(f52,plain,(
% 8.16/1.43    ( ! [X0,X3,X1] : (~sP8(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 8.16/1.43    inference(cnf_transformation,[],[f4])).
% 8.16/1.43  fof(f4,axiom,(
% 8.16/1.43    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 8.16/1.43  fof(f83,plain,(
% 8.16/1.43    ( ! [X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,k2_tarski(X0,X1))) )),
% 8.16/1.43    inference(equality_resolution,[],[f54])).
% 8.16/1.43  fof(f54,plain,(
% 8.16/1.43    ( ! [X2,X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 8.16/1.43    inference(cnf_transformation,[],[f4])).
% 8.16/1.43  fof(f101,plain,(
% 8.16/1.43    ( ! [X1] : (sK0 != sK5(X1) | ~r2_hidden(sK2,X1) | k1_xboole_0 = X1) ) | ~spl15_1),
% 8.16/1.43    inference(superposition,[],[f32,f98])).
% 8.16/1.43  fof(f98,plain,(
% 8.16/1.43    sK0 = k4_tarski(sK1,sK2) | ~spl15_1),
% 8.16/1.43    inference(avatar_component_clause,[],[f96])).
% 8.16/1.43  fof(f32,plain,(
% 8.16/1.43    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 8.16/1.43    inference(cnf_transformation,[],[f21])).
% 8.16/1.43  fof(f5375,plain,(
% 8.16/1.43    ( ! [X1] : (sK0 != sK5(X1) | ~r2_hidden(sK0,X1) | k1_xboole_0 = X1) ) | (~spl15_1 | ~spl15_2 | ~spl15_5)),
% 8.16/1.43    inference(forward_demodulation,[],[f101,f170])).
% 8.16/1.43  fof(f4842,plain,(
% 8.16/1.43    ~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16),
% 8.16/1.43    inference(avatar_contradiction_clause,[],[f4841])).
% 8.16/1.43  fof(f4841,plain,(
% 8.16/1.43    $false | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(subsumption_resolution,[],[f4654,f2683])).
% 8.16/1.43  fof(f4654,plain,(
% 8.16/1.43    ( ! [X33] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X33),sK2))) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(trivial_inequality_removal,[],[f4649])).
% 8.16/1.43  fof(f4649,plain,(
% 8.16/1.43    ( ! [X33] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X33),sK2)) | sK0 != sK0) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(superposition,[],[f1540,f4566])).
% 8.16/1.43  fof(f4566,plain,(
% 8.16/1.43    ( ! [X19] : (k1_xboole_0 = k2_tarski(X19,sK0) | sK0 != X19) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(subsumption_resolution,[],[f4561,f1519])).
% 8.16/1.43  fof(f4561,plain,(
% 8.16/1.43    ( ! [X19] : (sK0 != X19 | ~r2_hidden(sK0,k2_tarski(X19,sK0)) | k1_xboole_0 = k2_tarski(X19,sK0)) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(superposition,[],[f2646,f4524])).
% 8.16/1.43  fof(f4524,plain,(
% 8.16/1.43    ( ! [X1] : (sK5(k2_tarski(X1,sK0)) = X1) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(subsumption_resolution,[],[f4501,f2683])).
% 8.16/1.43  fof(f4501,plain,(
% 8.16/1.43    ( ! [X2,X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_tarski(X2),sK2)) | sK5(k2_tarski(X1,sK0)) = X1) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(superposition,[],[f1523,f4483])).
% 8.16/1.43  fof(f4483,plain,(
% 8.16/1.43    ( ! [X18] : (k1_xboole_0 = k2_tarski(X18,sK0) | sK5(k2_tarski(X18,sK0)) = X18) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(subsumption_resolution,[],[f4481,f1519])).
% 8.16/1.43  fof(f4481,plain,(
% 8.16/1.43    ( ! [X18] : (~r2_hidden(sK0,k2_tarski(X18,sK0)) | k1_xboole_0 = k2_tarski(X18,sK0) | sK5(k2_tarski(X18,sK0)) = X18) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(trivial_inequality_removal,[],[f4471])).
% 8.16/1.43  fof(f4471,plain,(
% 8.16/1.43    ( ! [X18] : (sK0 != sK0 | ~r2_hidden(sK0,k2_tarski(X18,sK0)) | k1_xboole_0 = k2_tarski(X18,sK0) | sK5(k2_tarski(X18,sK0)) = X18) ) | (~spl15_1 | ~spl15_5 | ~spl15_6 | ~spl15_15 | ~spl15_16)),
% 8.16/1.43    inference(superposition,[],[f2646,f4385])).
% 8.16/1.43  fof(f2646,plain,(
% 8.16/1.43    ( ! [X0] : (sK0 != sK5(X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X0) ) | (~spl15_1 | ~spl15_6 | ~spl15_16)),
% 8.16/1.43    inference(backward_demodulation,[],[f100,f2644])).
% 8.16/1.43  fof(f2644,plain,(
% 8.16/1.43    sK0 = sK1 | (~spl15_1 | ~spl15_6 | ~spl15_16)),
% 8.16/1.43    inference(backward_demodulation,[],[f2471,f201])).
% 8.16/1.43  fof(f201,plain,(
% 8.16/1.43    sK0 = k1_mcart_1(sK0) | (~spl15_1 | ~spl15_6)),
% 8.16/1.43    inference(backward_demodulation,[],[f102,f182])).
% 8.16/1.43  fof(f182,plain,(
% 8.16/1.43    sK0 = sK1 | (~spl15_1 | ~spl15_6)),
% 8.16/1.43    inference(forward_demodulation,[],[f102,f156])).
% 8.16/1.43  fof(f156,plain,(
% 8.16/1.43    sK0 = k1_mcart_1(sK0) | ~spl15_6),
% 8.16/1.43    inference(avatar_component_clause,[],[f154])).
% 8.16/1.43  fof(f154,plain,(
% 8.16/1.43    spl15_6 <=> sK0 = k1_mcart_1(sK0)),
% 8.16/1.43    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).
% 8.16/1.43  fof(f102,plain,(
% 8.16/1.43    sK1 = k1_mcart_1(sK0) | ~spl15_1),
% 8.16/1.43    inference(superposition,[],[f35,f98])).
% 8.16/1.43  fof(f35,plain,(
% 8.16/1.43    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 8.16/1.43    inference(cnf_transformation,[],[f14])).
% 8.16/1.43  fof(f14,axiom,(
% 8.16/1.43    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 8.16/1.43  fof(f2471,plain,(
% 8.16/1.43    sK1 = k1_mcart_1(sK0) | ~spl15_16),
% 8.16/1.43    inference(avatar_component_clause,[],[f2469])).
% 8.16/1.43  fof(f2469,plain,(
% 8.16/1.43    spl15_16 <=> sK1 = k1_mcart_1(sK0)),
% 8.16/1.43    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).
% 8.16/1.43  fof(f100,plain,(
% 8.16/1.43    ( ! [X0] : (sK0 != sK5(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl15_1),
% 8.16/1.43    inference(superposition,[],[f31,f98])).
% 8.16/1.43  fof(f31,plain,(
% 8.16/1.43    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 8.16/1.43    inference(cnf_transformation,[],[f21])).
% 8.16/1.43  fof(f1540,plain,(
% 8.16/1.43    ( ! [X2,X3] : (~r1_tarski(k2_tarski(sK0,X2),k2_zfmisc_1(k1_tarski(X3),sK2))) ) | ~spl15_5),
% 8.16/1.43    inference(resolution,[],[f1536,f1470])).
% 8.16/1.43  fof(f1536,plain,(
% 8.16/1.43    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 8.16/1.43    inference(superposition,[],[f1513,f34])).
% 8.16/1.43  fof(f1513,plain,(
% 8.16/1.43    ( ! [X4,X5,X3] : (r2_hidden(X3,k1_enumset1(X4,X3,X5))) )),
% 8.16/1.43    inference(resolution,[],[f91,f93])).
% 8.16/1.43  fof(f93,plain,(
% 8.16/1.43    ( ! [X4,X2,X0] : (sP14(X4,X2,X4,X0)) )),
% 8.16/1.43    inference(equality_resolution,[],[f67])).
% 8.16/1.43  fof(f67,plain,(
% 8.16/1.43    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP14(X4,X2,X1,X0)) )),
% 8.16/1.43    inference(cnf_transformation,[],[f25])).
% 8.16/1.43  fof(f2550,plain,(
% 8.16/1.43    spl15_15 | ~spl15_1 | ~spl15_2 | ~spl15_5),
% 8.16/1.43    inference(avatar_split_clause,[],[f2545,f136,f115,f96,f2380])).
% 8.16/1.43  fof(f2545,plain,(
% 8.16/1.43    k1_xboole_0 = k1_tarski(sK0) | (~spl15_1 | ~spl15_2 | ~spl15_5)),
% 8.16/1.43    inference(duplicate_literal_removal,[],[f2543])).
% 8.16/1.43  fof(f2543,plain,(
% 8.16/1.43    k1_xboole_0 = k1_tarski(sK0) | k1_xboole_0 = k1_tarski(sK0) | (~spl15_1 | ~spl15_2 | ~spl15_5)),
% 8.16/1.43    inference(resolution,[],[f2435,f2299])).
% 8.16/1.43  fof(f2299,plain,(
% 8.16/1.43    ( ! [X6] : (r2_hidden(X6,k1_tarski(X6)) | k1_xboole_0 = k1_tarski(X6)) )),
% 8.16/1.43    inference(duplicate_literal_removal,[],[f2286])).
% 8.16/1.43  fof(f2286,plain,(
% 8.16/1.43    ( ! [X6] : (r2_hidden(X6,k1_tarski(X6)) | k1_xboole_0 = k1_tarski(X6) | k1_xboole_0 = k1_tarski(X6)) )),
% 8.16/1.43    inference(superposition,[],[f33,f1670])).
% 8.16/1.43  fof(f1670,plain,(
% 8.16/1.43    ( ! [X2] : (sK5(k1_tarski(X2)) = X2 | k1_xboole_0 = k1_tarski(X2)) )),
% 8.16/1.43    inference(resolution,[],[f1666,f33])).
% 8.16/1.43  fof(f1666,plain,(
% 8.16/1.43    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 8.16/1.43    inference(condensation,[],[f1665])).
% 8.16/1.43  fof(f1665,plain,(
% 8.16/1.43    ( ! [X6,X4,X7,X5] : (X4 = X5 | ~r2_hidden(X4,k1_tarski(X5)) | ~r2_hidden(X6,X7)) )),
% 8.16/1.43    inference(forward_demodulation,[],[f1658,f35])).
% 8.16/1.43  fof(f1658,plain,(
% 8.16/1.43    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k1_tarski(X5)) | ~r2_hidden(X6,X7) | k1_mcart_1(k4_tarski(X4,X6)) = X5) )),
% 8.16/1.43    inference(resolution,[],[f1525,f48])).
% 8.16/1.43  fof(f48,plain,(
% 8.16/1.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 8.16/1.43    inference(cnf_transformation,[],[f24])).
% 8.16/1.43  fof(f1525,plain,(
% 8.16/1.43    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) | ~r2_hidden(X2,X3) | ~r2_hidden(X0,X1)) )),
% 8.16/1.43    inference(resolution,[],[f89,f88])).
% 8.16/1.43  fof(f88,plain,(
% 8.16/1.43    ( ! [X0,X3,X1] : (~sP10(X3,X1,X0) | r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 8.16/1.43    inference(equality_resolution,[],[f61])).
% 8.16/1.43  fof(f61,plain,(
% 8.16/1.43    ( ! [X2,X0,X3,X1] : (~sP10(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 8.16/1.43    inference(cnf_transformation,[],[f9])).
% 8.16/1.43  fof(f9,axiom,(
% 8.16/1.43    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 8.16/1.43  fof(f89,plain,(
% 8.16/1.43    ( ! [X4,X0,X5,X1] : (sP10(k4_tarski(X4,X5),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 8.16/1.43    inference(equality_resolution,[],[f57])).
% 8.16/1.43  fof(f57,plain,(
% 8.16/1.43    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP10(X3,X1,X0)) )),
% 8.16/1.43    inference(cnf_transformation,[],[f9])).
% 8.16/1.43  fof(f2435,plain,(
% 8.16/1.43    ( ! [X7] : (~r2_hidden(sK0,k1_tarski(X7)) | k1_xboole_0 = k1_tarski(X7)) ) | (~spl15_1 | ~spl15_2 | ~spl15_5)),
% 8.16/1.43    inference(subsumption_resolution,[],[f2422,f1666])).
% 8.16/1.43  fof(f2422,plain,(
% 8.16/1.43    ( ! [X7] : (~r2_hidden(sK0,k1_tarski(X7)) | sK0 != X7 | k1_xboole_0 = k1_tarski(X7)) ) | (~spl15_1 | ~spl15_2 | ~spl15_5)),
% 8.16/1.43    inference(backward_demodulation,[],[f2298,f170])).
% 8.16/1.43  fof(f2298,plain,(
% 8.16/1.43    ( ! [X7] : (~r2_hidden(sK2,k1_tarski(X7)) | sK0 != X7 | k1_xboole_0 = k1_tarski(X7)) ) | ~spl15_1),
% 8.16/1.43    inference(duplicate_literal_removal,[],[f2287])).
% 8.16/1.43  fof(f2287,plain,(
% 8.16/1.43    ( ! [X7] : (sK0 != X7 | ~r2_hidden(sK2,k1_tarski(X7)) | k1_xboole_0 = k1_tarski(X7) | k1_xboole_0 = k1_tarski(X7)) ) | ~spl15_1),
% 8.16/1.43    inference(superposition,[],[f101,f1670])).
% 8.16/1.43  fof(f2472,plain,(
% 8.16/1.43    spl15_16 | ~spl15_1),
% 8.16/1.43    inference(avatar_split_clause,[],[f102,f96,f2469])).
% 8.16/1.43  fof(f2383,plain,(
% 8.16/1.43    spl15_15 | ~spl15_1 | ~spl15_6),
% 8.16/1.43    inference(avatar_split_clause,[],[f2329,f154,f96,f2380])).
% 8.16/1.43  fof(f2329,plain,(
% 8.16/1.43    k1_xboole_0 = k1_tarski(sK0) | (~spl15_1 | ~spl15_6)),
% 8.16/1.43    inference(duplicate_literal_removal,[],[f2322])).
% 8.16/1.43  fof(f2322,plain,(
% 8.16/1.43    k1_xboole_0 = k1_tarski(sK0) | k1_xboole_0 = k1_tarski(sK0) | (~spl15_1 | ~spl15_6)),
% 8.16/1.43    inference(resolution,[],[f2299,f2302])).
% 8.16/1.43  fof(f2302,plain,(
% 8.16/1.43    ( ! [X8] : (~r2_hidden(sK0,k1_tarski(X8)) | k1_xboole_0 = k1_tarski(X8)) ) | (~spl15_1 | ~spl15_6)),
% 8.16/1.43    inference(subsumption_resolution,[],[f2297,f1666])).
% 8.16/1.43  fof(f2297,plain,(
% 8.16/1.43    ( ! [X8] : (sK0 != X8 | ~r2_hidden(sK0,k1_tarski(X8)) | k1_xboole_0 = k1_tarski(X8)) ) | (~spl15_1 | ~spl15_6)),
% 8.16/1.43    inference(duplicate_literal_removal,[],[f2288])).
% 8.16/1.43  fof(f2288,plain,(
% 8.16/1.43    ( ! [X8] : (sK0 != X8 | ~r2_hidden(sK0,k1_tarski(X8)) | k1_xboole_0 = k1_tarski(X8) | k1_xboole_0 = k1_tarski(X8)) ) | (~spl15_1 | ~spl15_6)),
% 8.16/1.43    inference(superposition,[],[f200,f1670])).
% 8.16/1.43  fof(f200,plain,(
% 8.16/1.43    ( ! [X0] : (sK0 != sK5(X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X0) ) | (~spl15_1 | ~spl15_6)),
% 8.16/1.43    inference(backward_demodulation,[],[f100,f182])).
% 8.16/1.43  fof(f157,plain,(
% 8.16/1.43    spl15_6 | ~spl15_1 | ~spl15_3),
% 8.16/1.43    inference(avatar_split_clause,[],[f125,f119,f96,f154])).
% 8.16/1.43  fof(f119,plain,(
% 8.16/1.43    spl15_3 <=> sK0 = sK1),
% 8.16/1.43    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).
% 8.16/1.43  fof(f125,plain,(
% 8.16/1.43    sK0 = k1_mcart_1(sK0) | (~spl15_1 | ~spl15_3)),
% 8.16/1.43    inference(backward_demodulation,[],[f102,f121])).
% 8.16/1.43  fof(f121,plain,(
% 8.16/1.43    sK0 = sK1 | ~spl15_3),
% 8.16/1.43    inference(avatar_component_clause,[],[f119])).
% 8.16/1.43  fof(f139,plain,(
% 8.16/1.43    spl15_5 | ~spl15_1),
% 8.16/1.43    inference(avatar_split_clause,[],[f103,f96,f136])).
% 8.16/1.43  fof(f103,plain,(
% 8.16/1.43    sK2 = k2_mcart_1(sK0) | ~spl15_1),
% 8.16/1.43    inference(superposition,[],[f36,f98])).
% 8.16/1.43  fof(f36,plain,(
% 8.16/1.43    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 8.16/1.43    inference(cnf_transformation,[],[f14])).
% 8.16/1.43  fof(f122,plain,(
% 8.16/1.43    spl15_2 | spl15_3 | ~spl15_1),
% 8.16/1.43    inference(avatar_split_clause,[],[f109,f96,f119,f115])).
% 8.16/1.43  fof(f109,plain,(
% 8.16/1.43    sK0 = sK1 | sK0 = k2_mcart_1(sK0) | ~spl15_1),
% 8.16/1.43    inference(backward_demodulation,[],[f26,f102])).
% 8.16/1.43  fof(f26,plain,(
% 8.16/1.43    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 8.16/1.43    inference(cnf_transformation,[],[f19])).
% 8.16/1.43  fof(f19,plain,(
% 8.16/1.43    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 8.16/1.43    inference(ennf_transformation,[],[f17])).
% 8.16/1.43  fof(f17,negated_conjecture,(
% 8.16/1.43    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 8.16/1.43    inference(negated_conjecture,[],[f16])).
% 8.16/1.43  fof(f16,conjecture,(
% 8.16/1.43    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 8.16/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 8.16/1.43  fof(f99,plain,(
% 8.16/1.43    spl15_1),
% 8.16/1.43    inference(avatar_split_clause,[],[f27,f96])).
% 8.16/1.43  fof(f27,plain,(
% 8.16/1.43    sK0 = k4_tarski(sK1,sK2)),
% 8.16/1.43    inference(cnf_transformation,[],[f19])).
% 8.16/1.43  % SZS output end Proof for theBenchmark
% 8.16/1.43  % (26642)------------------------------
% 8.16/1.43  % (26642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.16/1.43  % (26642)Termination reason: Refutation
% 8.16/1.43  
% 8.16/1.43  % (26642)Memory used [KB]: 15095
% 8.16/1.43  % (26642)Time elapsed: 1.0000 s
% 8.16/1.43  % (26642)------------------------------
% 8.16/1.43  % (26642)------------------------------
% 8.16/1.43  % (26621)Success in time 1.06 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:03 EST 2020

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 264 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  260 ( 594 expanded)
%              Number of equality atoms :   78 ( 187 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f85,f100,f120,f166,f342,f644,f717,f849,f1273])).

fof(f1273,plain,
    ( spl5_2
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f1272])).

fof(f1272,plain,
    ( $false
    | spl5_2
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1271,f1175])).

fof(f1175,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK0)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f70,f1173])).

fof(f1173,plain,
    ( sK0 = sK2
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f1164,f237])).

fof(f237,plain,
    ( ! [X1] : k1_xboole_0 != k1_tarski(X1)
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f60,f224])).

fof(f224,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10)
    | ~ spl5_5 ),
    inference(resolution,[],[f154,f140])).

fof(f140,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3
      | r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(resolution,[],[f33,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f154,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_xboole_0)
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,k1_xboole_0) )
    | ~ spl5_5 ),
    inference(superposition,[],[f58,f99])).

fof(f99,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_5
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1164,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2
    | ~ spl5_12 ),
    inference(resolution,[],[f848,f108])).

fof(f108,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(k1_tarski(X8),k1_tarski(X7))
      | k1_xboole_0 = k1_tarski(X8)
      | X7 = X8 ) ),
    inference(superposition,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f848,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f846])).

fof(f846,plain,
    ( spl5_12
  <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f70,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_2
  <=> k2_tarski(sK0,sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1271,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK0)
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f1239,f80])).

fof(f80,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(resolution,[],[f45,f54])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1239,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f716,f1173])).

fof(f716,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl5_11
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f849,plain,
    ( spl5_12
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f809,f117,f97,f846])).

fof(f117,plain,
    ( spl5_6
  <=> k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f809,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK2))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f755,f54])).

fof(f755,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k2_tarski(sK0,sK1))
        | r1_tarski(X4,k1_tarski(sK2)) )
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(superposition,[],[f269,f119])).

fof(f119,plain,
    ( k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f269,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X1,k2_xboole_0(X2,X0))
        | ~ r1_tarski(X1,X2) )
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f264,f230])).

fof(f230,plain,
    ( ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f104,f224])).

fof(f104,plain,(
    ! [X5] : k2_xboole_0(X5,k4_xboole_0(X5,X5)) = X5 ),
    inference(resolution,[],[f44,f90])).

fof(f90,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_xboole_0(X2,k1_xboole_0))
      | r1_tarski(X1,k2_xboole_0(X2,X0)) ) ),
    inference(superposition,[],[f126,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_xboole_0(X0,k3_xboole_0(X1,X2)))
      | r1_tarski(X3,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f49,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f717,plain,
    ( spl5_11
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f710,f117,f97,f714])).

fof(f710,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f702,f230])).

fof(f702,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k3_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0))
    | ~ spl5_6 ),
    inference(superposition,[],[f128,f48])).

fof(f128,plain,
    ( ! [X1] : k2_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)),X1)) = k3_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK0,sK1),X1))
    | ~ spl5_6 ),
    inference(superposition,[],[f38,f119])).

fof(f644,plain,
    ( spl5_10
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f227,f97,f641])).

fof(f641,plain,
    ( spl5_10
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f227,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f158,f223])).

fof(f223,plain,
    ( ! [X9] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9)
    | ~ spl5_5 ),
    inference(resolution,[],[f154,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f32])).

fof(f158,plain,
    ( ! [X1] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f157,f99])).

fof(f157,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f148,f48])).

fof(f148,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)
    | ~ spl5_5 ),
    inference(superposition,[],[f37,f99])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f342,plain,
    ( spl5_8
    | spl5_9
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f280,f82,f340,f336])).

fof(f336,plain,
    ( spl5_8
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f340,plain,
    ( spl5_9
  <=> ! [X0] : ~ r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f82,plain,
    ( spl5_4
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK2)))
        | k1_xboole_0 = k2_tarski(sK0,sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f251,f43])).

fof(f251,plain,
    ( ! [X8,X9] :
        ( r1_tarski(X8,k4_xboole_0(X9,k2_tarski(sK0,sK1)))
        | ~ r1_tarski(X8,k4_xboole_0(X9,k1_tarski(sK2))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f123,f84])).

fof(f84,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k4_xboole_0(X0,k3_xboole_0(X1,X2)))
      | ~ r1_tarski(X3,k4_xboole_0(X0,X2)) ) ),
    inference(superposition,[],[f50,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f166,plain,
    ( spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f146,f117,f163])).

fof(f163,plain,
    ( spl5_7
  <=> r1_tarski(k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f146,plain,
    ( r1_tarski(k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)),k1_tarski(sK2))
    | ~ spl5_6 ),
    inference(resolution,[],[f129,f90])).

fof(f129,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)))
        | r1_tarski(X2,k1_tarski(sK2)) )
    | ~ spl5_6 ),
    inference(superposition,[],[f50,f119])).

fof(f120,plain,
    ( spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f101,f63,f117])).

fof(f63,plain,
    ( spl5_1
  <=> r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f101,plain,
    ( k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)))
    | ~ spl5_1 ),
    inference(resolution,[],[f44,f65])).

fof(f65,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f100,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f78,f73,f97])).

fof(f73,plain,
    ( spl5_3
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f78,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_3 ),
    inference(resolution,[],[f42,f75])).

fof(f75,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f85,plain,
    ( spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f79,f63,f82])).

fof(f79,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f45,f65])).

fof(f76,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f61,f73])).

fof(f61,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f71,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f66,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (5573)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (5570)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (5598)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (5589)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (5583)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (5600)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (5592)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (5584)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (5587)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (5593)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (5568)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (5568)Refutation not found, incomplete strategy% (5568)------------------------------
% 0.21/0.53  % (5568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5568)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5568)Memory used [KB]: 1663
% 0.21/0.53  % (5568)Time elapsed: 0.123 s
% 0.21/0.53  % (5568)------------------------------
% 0.21/0.53  % (5568)------------------------------
% 0.21/0.53  % (5574)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (5571)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (5572)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (5592)Refutation not found, incomplete strategy% (5592)------------------------------
% 0.21/0.53  % (5592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5592)Memory used [KB]: 10746
% 0.21/0.53  % (5592)Time elapsed: 0.072 s
% 0.21/0.53  % (5582)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (5592)------------------------------
% 0.21/0.53  % (5592)------------------------------
% 0.21/0.53  % (5576)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (5594)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (5588)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (5581)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (5591)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (5579)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (5579)Refutation not found, incomplete strategy% (5579)------------------------------
% 0.21/0.54  % (5579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5579)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5579)Memory used [KB]: 10618
% 0.21/0.54  % (5579)Time elapsed: 0.135 s
% 0.21/0.54  % (5579)------------------------------
% 0.21/0.54  % (5579)------------------------------
% 0.21/0.54  % (5585)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (5578)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (5578)Refutation not found, incomplete strategy% (5578)------------------------------
% 0.21/0.55  % (5578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5578)Memory used [KB]: 10618
% 0.21/0.55  % (5578)Time elapsed: 0.148 s
% 0.21/0.55  % (5578)------------------------------
% 0.21/0.55  % (5578)------------------------------
% 0.21/0.55  % (5577)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.57/0.56  % (5599)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.56  % (5601)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.56  % (5575)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.57/0.56  % (5580)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.57/0.56  % (5580)Refutation not found, incomplete strategy% (5580)------------------------------
% 1.57/0.56  % (5580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (5580)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (5580)Memory used [KB]: 10618
% 1.57/0.56  % (5580)Time elapsed: 0.154 s
% 1.57/0.56  % (5580)------------------------------
% 1.57/0.56  % (5580)------------------------------
% 1.57/0.57  % (5596)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.70/0.58  % (5586)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.70/0.59  % (5586)Refutation not found, incomplete strategy% (5586)------------------------------
% 1.70/0.59  % (5586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (5586)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (5586)Memory used [KB]: 10618
% 1.70/0.59  % (5586)Time elapsed: 0.186 s
% 1.70/0.59  % (5586)------------------------------
% 1.70/0.59  % (5586)------------------------------
% 2.09/0.64  % (5662)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.28/0.66  % (5661)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.28/0.66  % (5661)Refutation not found, incomplete strategy% (5661)------------------------------
% 2.28/0.66  % (5661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.66  % (5661)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.66  
% 2.28/0.66  % (5661)Memory used [KB]: 6140
% 2.28/0.66  % (5661)Time elapsed: 0.096 s
% 2.28/0.66  % (5661)------------------------------
% 2.28/0.66  % (5661)------------------------------
% 2.28/0.68  % (5663)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.28/0.68  % (5664)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.28/0.70  % (5665)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.74/0.73  % (5666)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.01/0.77  % (5570)Refutation found. Thanks to Tanya!
% 3.01/0.77  % SZS status Theorem for theBenchmark
% 3.01/0.77  % SZS output start Proof for theBenchmark
% 3.01/0.77  fof(f1279,plain,(
% 3.01/0.77    $false),
% 3.01/0.77    inference(avatar_sat_refutation,[],[f66,f71,f76,f85,f100,f120,f166,f342,f644,f717,f849,f1273])).
% 3.01/0.77  fof(f1273,plain,(
% 3.01/0.77    spl5_2 | ~spl5_5 | ~spl5_11 | ~spl5_12),
% 3.01/0.77    inference(avatar_contradiction_clause,[],[f1272])).
% 3.01/0.77  fof(f1272,plain,(
% 3.01/0.77    $false | (spl5_2 | ~spl5_5 | ~spl5_11 | ~spl5_12)),
% 3.01/0.77    inference(subsumption_resolution,[],[f1271,f1175])).
% 3.01/0.77  fof(f1175,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) != k1_tarski(sK0) | (spl5_2 | ~spl5_5 | ~spl5_12)),
% 3.01/0.77    inference(backward_demodulation,[],[f70,f1173])).
% 3.01/0.77  fof(f1173,plain,(
% 3.01/0.77    sK0 = sK2 | (~spl5_5 | ~spl5_12)),
% 3.01/0.77    inference(subsumption_resolution,[],[f1164,f237])).
% 3.01/0.77  fof(f237,plain,(
% 3.01/0.77    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) ) | ~spl5_5),
% 3.01/0.77    inference(backward_demodulation,[],[f60,f224])).
% 3.01/0.77  fof(f224,plain,(
% 3.01/0.77    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(X10,X10)) ) | ~spl5_5),
% 3.01/0.77    inference(resolution,[],[f154,f140])).
% 3.01/0.77  fof(f140,plain,(
% 3.01/0.77    ( ! [X2,X3] : (r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 3.01/0.77    inference(duplicate_literal_removal,[],[f138])).
% 3.01/0.77  fof(f138,plain,(
% 3.01/0.77    ( ! [X2,X3] : (r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3 | r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 3.01/0.77    inference(resolution,[],[f33,f32])).
% 3.01/0.77  fof(f32,plain,(
% 3.01/0.77    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 3.01/0.77    inference(cnf_transformation,[],[f2])).
% 3.01/0.77  fof(f2,axiom,(
% 3.01/0.77    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.01/0.77  fof(f33,plain,(
% 3.01/0.77    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 3.01/0.77    inference(cnf_transformation,[],[f2])).
% 3.01/0.77  fof(f154,plain,(
% 3.01/0.77    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) ) | ~spl5_5),
% 3.01/0.77    inference(duplicate_literal_removal,[],[f152])).
% 3.01/0.77  fof(f152,plain,(
% 3.01/0.77    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k1_xboole_0)) ) | ~spl5_5),
% 3.01/0.77    inference(superposition,[],[f58,f99])).
% 3.01/0.77  fof(f99,plain,(
% 3.01/0.77    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_5),
% 3.01/0.77    inference(avatar_component_clause,[],[f97])).
% 3.01/0.77  fof(f97,plain,(
% 3.01/0.77    spl5_5 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.01/0.77  fof(f58,plain,(
% 3.01/0.77    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 3.01/0.77    inference(equality_resolution,[],[f35])).
% 3.01/0.77  fof(f35,plain,(
% 3.01/0.77    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.01/0.77    inference(cnf_transformation,[],[f2])).
% 3.01/0.77  fof(f60,plain,(
% 3.01/0.77    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 3.01/0.77    inference(equality_resolution,[],[f40])).
% 3.01/0.77  fof(f40,plain,(
% 3.01/0.77    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.01/0.77    inference(cnf_transformation,[],[f18])).
% 3.01/0.77  fof(f18,axiom,(
% 3.01/0.77    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 3.01/0.77  fof(f1164,plain,(
% 3.01/0.77    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2 | ~spl5_12),
% 3.01/0.77    inference(resolution,[],[f848,f108])).
% 3.01/0.77  fof(f108,plain,(
% 3.01/0.77    ( ! [X8,X7] : (~r1_tarski(k1_tarski(X8),k1_tarski(X7)) | k1_xboole_0 = k1_tarski(X8) | X7 = X8) )),
% 3.01/0.77    inference(superposition,[],[f43,f39])).
% 3.01/0.77  fof(f39,plain,(
% 3.01/0.77    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.01/0.77    inference(cnf_transformation,[],[f18])).
% 3.01/0.77  fof(f43,plain,(
% 3.01/0.77    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 3.01/0.77    inference(cnf_transformation,[],[f22])).
% 3.01/0.77  fof(f22,plain,(
% 3.01/0.77    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.01/0.77    inference(ennf_transformation,[],[f10])).
% 3.01/0.77  fof(f10,axiom,(
% 3.01/0.77    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 3.01/0.77  fof(f848,plain,(
% 3.01/0.77    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) | ~spl5_12),
% 3.01/0.77    inference(avatar_component_clause,[],[f846])).
% 3.01/0.77  fof(f846,plain,(
% 3.01/0.77    spl5_12 <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK2))),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.01/0.77  fof(f70,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) != k1_tarski(sK2) | spl5_2),
% 3.01/0.77    inference(avatar_component_clause,[],[f68])).
% 3.01/0.77  fof(f68,plain,(
% 3.01/0.77    spl5_2 <=> k2_tarski(sK0,sK1) = k1_tarski(sK2)),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.01/0.77  fof(f1271,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) = k1_tarski(sK0) | (~spl5_5 | ~spl5_11 | ~spl5_12)),
% 3.01/0.77    inference(forward_demodulation,[],[f1239,f80])).
% 3.01/0.77  fof(f80,plain,(
% 3.01/0.77    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.01/0.77    inference(resolution,[],[f45,f54])).
% 3.01/0.77  fof(f54,plain,(
% 3.01/0.77    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.01/0.77    inference(cnf_transformation,[],[f17])).
% 3.01/0.77  fof(f17,axiom,(
% 3.01/0.77    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 3.01/0.77  fof(f45,plain,(
% 3.01/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.01/0.77    inference(cnf_transformation,[],[f24])).
% 3.01/0.77  fof(f24,plain,(
% 3.01/0.77    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.01/0.77    inference(ennf_transformation,[],[f8])).
% 3.01/0.77  fof(f8,axiom,(
% 3.01/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.01/0.77  fof(f1239,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) | (~spl5_5 | ~spl5_11 | ~spl5_12)),
% 3.01/0.77    inference(backward_demodulation,[],[f716,f1173])).
% 3.01/0.77  fof(f716,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) | ~spl5_11),
% 3.01/0.77    inference(avatar_component_clause,[],[f714])).
% 3.01/0.77  fof(f714,plain,(
% 3.01/0.77    spl5_11 <=> k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.01/0.77  fof(f849,plain,(
% 3.01/0.77    spl5_12 | ~spl5_5 | ~spl5_6),
% 3.01/0.77    inference(avatar_split_clause,[],[f809,f117,f97,f846])).
% 3.01/0.77  fof(f117,plain,(
% 3.01/0.77    spl5_6 <=> k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)))),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.01/0.77  fof(f809,plain,(
% 3.01/0.77    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) | (~spl5_5 | ~spl5_6)),
% 3.01/0.77    inference(resolution,[],[f755,f54])).
% 3.01/0.77  fof(f755,plain,(
% 3.01/0.77    ( ! [X4] : (~r1_tarski(X4,k2_tarski(sK0,sK1)) | r1_tarski(X4,k1_tarski(sK2))) ) | (~spl5_5 | ~spl5_6)),
% 3.01/0.77    inference(superposition,[],[f269,f119])).
% 3.01/0.77  fof(f119,plain,(
% 3.01/0.77    k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) | ~spl5_6),
% 3.01/0.77    inference(avatar_component_clause,[],[f117])).
% 3.01/0.77  fof(f269,plain,(
% 3.01/0.77    ( ! [X2,X0,X1] : (r1_tarski(X1,k2_xboole_0(X2,X0)) | ~r1_tarski(X1,X2)) ) | ~spl5_5),
% 3.01/0.77    inference(forward_demodulation,[],[f264,f230])).
% 3.01/0.77  fof(f230,plain,(
% 3.01/0.77    ( ! [X5] : (k2_xboole_0(X5,k1_xboole_0) = X5) ) | ~spl5_5),
% 3.01/0.77    inference(backward_demodulation,[],[f104,f224])).
% 3.01/0.77  fof(f104,plain,(
% 3.01/0.77    ( ! [X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X5)) = X5) )),
% 3.01/0.77    inference(resolution,[],[f44,f90])).
% 3.01/0.77  fof(f90,plain,(
% 3.01/0.77    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.01/0.77    inference(duplicate_literal_removal,[],[f89])).
% 3.01/0.77  fof(f89,plain,(
% 3.01/0.77    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 3.01/0.77    inference(resolution,[],[f53,f52])).
% 3.01/0.77  fof(f52,plain,(
% 3.01/0.77    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.01/0.77    inference(cnf_transformation,[],[f28])).
% 3.01/0.77  fof(f28,plain,(
% 3.01/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.01/0.77    inference(ennf_transformation,[],[f1])).
% 3.01/0.77  fof(f1,axiom,(
% 3.01/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.01/0.77  fof(f53,plain,(
% 3.01/0.77    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.01/0.77    inference(cnf_transformation,[],[f28])).
% 3.01/0.77  fof(f44,plain,(
% 3.01/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 3.01/0.77    inference(cnf_transformation,[],[f23])).
% 3.01/0.77  fof(f23,plain,(
% 3.01/0.77    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 3.01/0.77    inference(ennf_transformation,[],[f11])).
% 3.01/0.77  fof(f11,axiom,(
% 3.01/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 3.01/0.77  fof(f264,plain,(
% 3.01/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X1,k2_xboole_0(X2,k1_xboole_0)) | r1_tarski(X1,k2_xboole_0(X2,X0))) )),
% 3.01/0.77    inference(superposition,[],[f126,f48])).
% 3.01/0.77  fof(f48,plain,(
% 3.01/0.77    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.01/0.77    inference(cnf_transformation,[],[f9])).
% 3.01/0.77  fof(f9,axiom,(
% 3.01/0.77    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 3.01/0.77  fof(f126,plain,(
% 3.01/0.77    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_xboole_0(X0,k3_xboole_0(X1,X2))) | r1_tarski(X3,k2_xboole_0(X0,X1))) )),
% 3.01/0.77    inference(superposition,[],[f49,f38])).
% 3.01/0.77  fof(f38,plain,(
% 3.01/0.77    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 3.01/0.77    inference(cnf_transformation,[],[f7])).
% 3.01/0.77  fof(f7,axiom,(
% 3.01/0.77    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 3.01/0.77  fof(f49,plain,(
% 3.01/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 3.01/0.77    inference(cnf_transformation,[],[f26])).
% 3.01/0.77  fof(f26,plain,(
% 3.01/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.01/0.77    inference(ennf_transformation,[],[f6])).
% 3.01/0.77  fof(f6,axiom,(
% 3.01/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 3.01/0.77  fof(f717,plain,(
% 3.01/0.77    spl5_11 | ~spl5_5 | ~spl5_6),
% 3.01/0.77    inference(avatar_split_clause,[],[f710,f117,f97,f714])).
% 3.01/0.77  fof(f710,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) | (~spl5_5 | ~spl5_6)),
% 3.01/0.77    inference(forward_demodulation,[],[f702,f230])).
% 3.01/0.77  fof(f702,plain,(
% 3.01/0.77    k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k3_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)) | ~spl5_6),
% 3.01/0.77    inference(superposition,[],[f128,f48])).
% 3.01/0.77  fof(f128,plain,(
% 3.01/0.77    ( ! [X1] : (k2_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)),X1)) = k3_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_tarski(sK0,sK1),X1))) ) | ~spl5_6),
% 3.01/0.77    inference(superposition,[],[f38,f119])).
% 3.01/0.77  fof(f644,plain,(
% 3.01/0.77    spl5_10 | ~spl5_5),
% 3.01/0.77    inference(avatar_split_clause,[],[f227,f97,f641])).
% 3.01/0.77  fof(f641,plain,(
% 3.01/0.77    spl5_10 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.01/0.77  fof(f227,plain,(
% 3.01/0.77    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_5),
% 3.01/0.77    inference(backward_demodulation,[],[f158,f223])).
% 3.01/0.77  fof(f223,plain,(
% 3.01/0.77    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9)) ) | ~spl5_5),
% 3.01/0.77    inference(resolution,[],[f154,f136])).
% 3.01/0.77  fof(f136,plain,(
% 3.01/0.77    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 3.01/0.77    inference(factoring,[],[f32])).
% 3.01/0.77  fof(f158,plain,(
% 3.01/0.77    ( ! [X1] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) ) | ~spl5_5),
% 3.01/0.77    inference(forward_demodulation,[],[f157,f99])).
% 3.01/0.77  fof(f157,plain,(
% 3.01/0.77    ( ! [X1] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) ) | ~spl5_5),
% 3.01/0.77    inference(forward_demodulation,[],[f148,f48])).
% 3.01/0.77  fof(f148,plain,(
% 3.01/0.77    ( ! [X1] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) ) | ~spl5_5),
% 3.01/0.77    inference(superposition,[],[f37,f99])).
% 3.01/0.77  fof(f37,plain,(
% 3.01/0.77    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 3.01/0.77    inference(cnf_transformation,[],[f4])).
% 3.01/0.77  fof(f4,axiom,(
% 3.01/0.77    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 3.01/0.77  fof(f342,plain,(
% 3.01/0.77    spl5_8 | spl5_9 | ~spl5_4),
% 3.01/0.77    inference(avatar_split_clause,[],[f280,f82,f340,f336])).
% 3.01/0.77  fof(f336,plain,(
% 3.01/0.77    spl5_8 <=> k1_xboole_0 = k2_tarski(sK0,sK1)),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.01/0.77  fof(f340,plain,(
% 3.01/0.77    spl5_9 <=> ! [X0] : ~r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK2)))),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.01/0.77  fof(f82,plain,(
% 3.01/0.77    spl5_4 <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.01/0.77  fof(f280,plain,(
% 3.01/0.77    ( ! [X0] : (~r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK2))) | k1_xboole_0 = k2_tarski(sK0,sK1)) ) | ~spl5_4),
% 3.01/0.77    inference(resolution,[],[f251,f43])).
% 3.01/0.77  fof(f251,plain,(
% 3.01/0.77    ( ! [X8,X9] : (r1_tarski(X8,k4_xboole_0(X9,k2_tarski(sK0,sK1))) | ~r1_tarski(X8,k4_xboole_0(X9,k1_tarski(sK2)))) ) | ~spl5_4),
% 3.01/0.77    inference(superposition,[],[f123,f84])).
% 3.01/0.77  fof(f84,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) | ~spl5_4),
% 3.01/0.77    inference(avatar_component_clause,[],[f82])).
% 3.01/0.77  fof(f123,plain,(
% 3.01/0.77    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k4_xboole_0(X0,k3_xboole_0(X1,X2))) | ~r1_tarski(X3,k4_xboole_0(X0,X2))) )),
% 3.01/0.77    inference(superposition,[],[f50,f37])).
% 3.01/0.77  fof(f50,plain,(
% 3.01/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.01/0.77    inference(cnf_transformation,[],[f27])).
% 3.01/0.77  fof(f27,plain,(
% 3.01/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.01/0.77    inference(ennf_transformation,[],[f5])).
% 3.01/0.77  fof(f5,axiom,(
% 3.01/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.01/0.77  fof(f166,plain,(
% 3.01/0.77    spl5_7 | ~spl5_6),
% 3.01/0.77    inference(avatar_split_clause,[],[f146,f117,f163])).
% 3.01/0.77  fof(f163,plain,(
% 3.01/0.77    spl5_7 <=> r1_tarski(k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)),k1_tarski(sK2))),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.01/0.77  fof(f146,plain,(
% 3.01/0.77    r1_tarski(k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)),k1_tarski(sK2)) | ~spl5_6),
% 3.01/0.77    inference(resolution,[],[f129,f90])).
% 3.01/0.77  fof(f129,plain,(
% 3.01/0.77    ( ! [X2] : (~r1_tarski(X2,k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) | r1_tarski(X2,k1_tarski(sK2))) ) | ~spl5_6),
% 3.01/0.77    inference(superposition,[],[f50,f119])).
% 3.01/0.77  fof(f120,plain,(
% 3.01/0.77    spl5_6 | ~spl5_1),
% 3.01/0.77    inference(avatar_split_clause,[],[f101,f63,f117])).
% 3.01/0.77  fof(f63,plain,(
% 3.01/0.77    spl5_1 <=> r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.01/0.77  fof(f101,plain,(
% 3.01/0.77    k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) | ~spl5_1),
% 3.01/0.77    inference(resolution,[],[f44,f65])).
% 3.01/0.77  fof(f65,plain,(
% 3.01/0.77    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) | ~spl5_1),
% 3.01/0.77    inference(avatar_component_clause,[],[f63])).
% 3.01/0.77  fof(f100,plain,(
% 3.01/0.77    spl5_5 | ~spl5_3),
% 3.01/0.77    inference(avatar_split_clause,[],[f78,f73,f97])).
% 3.01/0.77  fof(f73,plain,(
% 3.01/0.77    spl5_3 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.01/0.77    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.01/0.77  fof(f78,plain,(
% 3.01/0.77    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_3),
% 3.01/0.77    inference(resolution,[],[f42,f75])).
% 3.01/0.77  fof(f75,plain,(
% 3.01/0.77    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_3),
% 3.01/0.77    inference(avatar_component_clause,[],[f73])).
% 3.01/0.77  fof(f42,plain,(
% 3.01/0.77    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 3.01/0.77    inference(cnf_transformation,[],[f13])).
% 3.01/0.77  fof(f13,axiom,(
% 3.01/0.77    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.01/0.77  fof(f85,plain,(
% 3.01/0.77    spl5_4 | ~spl5_1),
% 3.01/0.77    inference(avatar_split_clause,[],[f79,f63,f82])).
% 3.01/0.77  fof(f79,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) | ~spl5_1),
% 3.01/0.77    inference(resolution,[],[f45,f65])).
% 3.01/0.77  fof(f76,plain,(
% 3.01/0.77    spl5_3),
% 3.01/0.77    inference(avatar_split_clause,[],[f61,f73])).
% 3.01/0.77  fof(f61,plain,(
% 3.01/0.77    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.01/0.77    inference(equality_resolution,[],[f47])).
% 3.01/0.77  fof(f47,plain,(
% 3.01/0.77    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 3.01/0.77    inference(cnf_transformation,[],[f25])).
% 3.01/0.77  fof(f25,plain,(
% 3.01/0.77    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.01/0.77    inference(ennf_transformation,[],[f12])).
% 3.01/0.77  fof(f12,axiom,(
% 3.01/0.77    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 3.01/0.77  fof(f71,plain,(
% 3.01/0.77    ~spl5_2),
% 3.01/0.77    inference(avatar_split_clause,[],[f30,f68])).
% 3.01/0.77  fof(f30,plain,(
% 3.01/0.77    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 3.01/0.77    inference(cnf_transformation,[],[f21])).
% 3.01/0.77  fof(f21,plain,(
% 3.01/0.77    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 3.01/0.77    inference(ennf_transformation,[],[f20])).
% 3.01/0.77  fof(f20,negated_conjecture,(
% 3.01/0.77    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 3.01/0.77    inference(negated_conjecture,[],[f19])).
% 3.01/0.77  fof(f19,conjecture,(
% 3.01/0.77    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 3.01/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 3.01/0.77  fof(f66,plain,(
% 3.01/0.77    spl5_1),
% 3.01/0.77    inference(avatar_split_clause,[],[f29,f63])).
% 3.01/0.77  fof(f29,plain,(
% 3.01/0.77    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 3.01/0.77    inference(cnf_transformation,[],[f21])).
% 3.01/0.77  % SZS output end Proof for theBenchmark
% 3.01/0.77  % (5570)------------------------------
% 3.01/0.77  % (5570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.77  % (5570)Termination reason: Refutation
% 3.01/0.77  
% 3.01/0.77  % (5570)Memory used [KB]: 7803
% 3.01/0.77  % (5570)Time elapsed: 0.339 s
% 3.01/0.77  % (5570)------------------------------
% 3.01/0.77  % (5570)------------------------------
% 3.01/0.77  % (5563)Success in time 0.416 s
%------------------------------------------------------------------------------
